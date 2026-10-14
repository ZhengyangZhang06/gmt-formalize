# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.compactness_of_minimizing_currents-a1.mass_representation-a1.covector_euclidean_equiv-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-compactness-of-minimizing-currents-a1-mass-representation-a1-cov-64249b6f60/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.compactness_of_minimizing_currents-a1.mass_representation-a1`
- Child key: `covector_euclidean_equiv`
- Declaration: `Submission.cmr_covector_euclidean_equiv`
- Exact Lean type: `∀ (P n : ℕ), ∃ (d : ℕ) (c : Covector (Euclid P) n ≃L[ℝ] EuclideanSpace ℝ (Fin d)), ∀ α : Covector (Euclid P) n, covectorEuclideanNorm α = ‖c α‖`

## Sibling prerequisites

- `root.minimizing_implies_stationary-a1.covector_gram_bounds-a1`

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
