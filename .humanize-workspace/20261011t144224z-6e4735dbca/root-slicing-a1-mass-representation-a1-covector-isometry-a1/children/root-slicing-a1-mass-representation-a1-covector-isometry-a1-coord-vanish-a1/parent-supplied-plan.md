# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.slicing-a1.mass_representation-a1.covector_isometry-a1.coord_vanish-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/nodes/root-slicing-a1-mass-representation-a1-covector-isometry-a1-coord-vanish-a1/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.slicing-a1.mass_representation-a1.covector_isometry-a1`
- Child key: `coord_vanish`
- Declaration: `Submission.smr_ci_covector_eq_zero_of_coord`
- Exact Lean type: `∀ (P k : ℕ) (α : Covector (Eucl P) k), (∀ I : SimonMultiIndex k P, euclideanCovectorCoordinate α I = 0) → α = 0`

## Sibling prerequisites

- None.

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
