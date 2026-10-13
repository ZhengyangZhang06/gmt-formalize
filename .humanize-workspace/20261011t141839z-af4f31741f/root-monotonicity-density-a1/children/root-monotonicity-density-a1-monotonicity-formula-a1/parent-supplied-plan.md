# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.monotonicity_density-a1.monotonicity_formula-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T141839Z-af4f31741f/nodes/root-monotonicity-density-a1-monotonicity-formula-a1/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.monotonicity_density-a1`
- Child key: `monotonicity_formula`
- Declaration: `Submission.monotonicity_formula_8_3_3`
- Exact Lean type: `MonotonicityFormula`

## Sibling prerequisites

- None.

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
