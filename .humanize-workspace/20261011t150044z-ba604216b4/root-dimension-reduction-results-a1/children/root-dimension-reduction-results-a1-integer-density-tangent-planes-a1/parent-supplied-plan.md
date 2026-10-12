# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.dimension_reduction_results-a1.integer_density_tangent_planes-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-dimension-reduction-results-a1-integer-density-tangent-planes-a1/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.dimension_reduction_results-a1`
- Child key: `integer_density_tangent_planes`
- Declaration: `Submission.dimred_integer_density_and_tangent_planes`
- Exact Lean type: `IntegerDensityAndTangentPlanes`

## Sibling prerequisites

- `root.dimension_reduction_results-a1.im_mass_measure-a1`
- `root.dimension_reduction_results-a1.zero_dim_vanishing-a1`
- `root.dimension_reduction_results-a1.monotonicity-a1`
- `root.dimension_reduction_results-a1.moving_blowups-a1`
- `root.dimension_reduction_results-a1.one_dim_cones-a1`
- `root.dimension_reduction_results-a1.cone_splitting-a1`
- `root.dimension_reduction_results-a1.threshold_reduction-a1`

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
