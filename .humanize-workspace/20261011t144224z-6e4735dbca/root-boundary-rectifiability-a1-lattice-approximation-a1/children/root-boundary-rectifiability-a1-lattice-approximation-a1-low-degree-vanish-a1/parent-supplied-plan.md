# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.boundary_rectifiability-a1.lattice_approximation-a1.low_degree_vanish-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/nodes/root-boundary-rectifiability-a1-lattice-approximation-a1-low-degree-vanish-a1/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.boundary_rectifiability-a1.lattice_approximation-a1`
- Child key: `low_degree_vanish`
- Declaration: `Submission.br_la_apply_eq_zero_of_lt_degree`
- Exact Lean type: `∀ (P n : ℕ) (U : Set (Eucl P)) (X : GeometricCurrentOn U n), P < n → ∀ ω : TestFormOn U n, X ω = 0`

## Sibling prerequisites

- None.

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
