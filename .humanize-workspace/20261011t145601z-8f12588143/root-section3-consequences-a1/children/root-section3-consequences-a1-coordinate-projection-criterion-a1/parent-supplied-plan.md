# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.section3_consequences-a1.coordinate_projection_criterion-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T145601Z-8f12588143/nodes/root-section3-consequences-a1-coordinate-projection-criterion-a1/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.section3_consequences-a1`
- Child key: `coordinate_projection_criterion`
- Declaration: `Submission.section3_coordinateProjectionCriterion_of_submanifoldCover`
- Exact Lean type: `SubmanifoldCoverCharacterization → CoordinateProjectionCriterion`

## Sibling prerequisites

- `root.section3_consequences-a1.c1_image_null-a1`
- `root.section3_consequences-a1.chart_projection_positive-a1`

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
