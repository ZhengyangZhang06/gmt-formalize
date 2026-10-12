# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.polyhedral_approximation-a1.pairing_expansion-a1.coordinate_bound-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/nodes/root-polyhedral-approximation-a1-pairing-expansion-a1-coordinate-bound-a1/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.polyhedral_approximation-a1.pairing_expansion-a1`
- Child key: `coordinate_bound`
- Declaration: `Submission.polyhedral_approx_pairing_coordinate_bound`
- Exact Lean type: `∀ (P n : ℕ) (c : Covector (Eucl P) n) (I : SimonMultiIndex n P), |euclideanCovectorCoordinate c I| ≤ covectorEuclideanNorm c`

## Sibling prerequisites

- None.

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
