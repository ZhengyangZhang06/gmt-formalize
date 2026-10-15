# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.regular_components_are_minimizing-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-regular-components-are-minimizing-a1/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root`
- Child key: `regular_components_are_minimizing`
- Declaration: `Submission.regular_components_are_minimizing`
- Exact Lean type: `RegularComponentsAreMinimizing`

## Sibling prerequisites

- `root.minimizing_implies_stationary-a1`
- `root.dimension_reduction_results-a1`

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
