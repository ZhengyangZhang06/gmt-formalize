# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.existence_of_minimizing_filling-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-existence-of-minimizing-filling-a1/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root`
- Child key: `existence_of_minimizing_filling`
- Declaration: `Submission.existence_of_minimizing_filling`
- Exact Lean type: `ExistenceOfMinimizingFilling`

## Sibling prerequisites

- None.

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
