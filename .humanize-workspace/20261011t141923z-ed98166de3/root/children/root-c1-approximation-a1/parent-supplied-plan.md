# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.c1_approximation-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T141923Z-ed98166de3/nodes/root-c1-approximation-a1/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root`
- Child key: `c1_approximation`
- Declaration: `Submission.c1_approximation_theorem`
- Exact Lean type: `C1Approximation`

## Sibling prerequisites

- `root.lipschitz_ext_rademacher-a1`
- `root.whitney_extension-a1`

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
