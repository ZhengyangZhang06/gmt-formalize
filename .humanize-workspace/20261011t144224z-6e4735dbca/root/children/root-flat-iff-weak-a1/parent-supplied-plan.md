# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.flat_iff_weak-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/nodes/root-flat-iff-weak-a1/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root`
- Child key: `flat_iff_weak`
- Declaration: `Submission.flat_convergence_iff_weak_convergence`
- Exact Lean type: `FlatConvergenceIffWeakConvergence`

## Sibling prerequisites

- `root.deformation-a1`
- `root.slicing-a1`
- `root.boundary_rectifiability-a1`

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
