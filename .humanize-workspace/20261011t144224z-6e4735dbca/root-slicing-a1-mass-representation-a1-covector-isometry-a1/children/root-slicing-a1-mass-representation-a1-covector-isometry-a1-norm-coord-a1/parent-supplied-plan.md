# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.slicing-a1.mass_representation-a1.covector_isometry-a1.norm_coord-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/nodes/root-slicing-a1-mass-representation-a1-covector-isometry-a1-norm-coord-a1/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.slicing-a1.mass_representation-a1.covector_isometry-a1`
- Child key: `norm_coord`
- Declaration: `Submission.smr_ci_norm_eq_sqrt_sum_coord_sq`
- Exact Lean type: `∀ (P k : ℕ) (α : Covector (Eucl P) k), covectorEuclideanNorm α = Real.sqrt (∑ I : SimonMultiIndex k P, euclideanCovectorCoordinate α I ^ 2)`

## Sibling prerequisites

- None.

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
