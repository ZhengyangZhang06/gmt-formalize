# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.compactness_mass_bounds-a1.covector_expansion-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/nodes/root-compactness-mass-bounds-a1-covector-expansion-a1/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.compactness_mass_bounds-a1`
- Child key: `covector_expansion`
- Declaration: `Submission.cmb_covector_eq_sum_coord_smul_wedge`
- Exact Lean type: `∀ (P n : ℕ) (α : Covector (Eucl P) n), α = ∑ β : SimonMultiIndex n P, euclideanCovectorCoordinate α β • wedgeCovectors n (fun j => EuclideanSpace.proj (β j))`

## Sibling prerequisites

- None.

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
