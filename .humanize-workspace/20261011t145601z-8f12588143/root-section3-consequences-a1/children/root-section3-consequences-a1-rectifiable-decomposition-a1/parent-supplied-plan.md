# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.section3_consequences-a1.rectifiable_decomposition-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T145601Z-8f12588143/nodes/root-section3-consequences-a1-rectifiable-decomposition-a1/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.section3_consequences-a1`
- Child key: `rectifiable_decomposition`
- Declaration: `Submission.section3_rectifiableDecomposition`
- Exact Lean type: `RectifiableDecomposition`

## Sibling prerequisites

- None.

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
