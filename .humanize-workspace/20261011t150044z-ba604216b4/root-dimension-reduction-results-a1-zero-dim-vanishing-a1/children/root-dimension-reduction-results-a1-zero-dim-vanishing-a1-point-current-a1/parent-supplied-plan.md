# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.dimension_reduction_results-a1.zero_dim_vanishing-a1.point_current-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-dimension-reduction-results-a1-zero-dim-vanishing-a1-point-current-a1/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.dimension_reduction_results-a1.zero_dim_vanishing-a1`
- Child key: `point_current`
- Declaration: `Submission.dimred_zdv_point_current`
- Exact Lean type: `∀ (P n : ℕ) (U : Set (Euclid P)) (p : Euclid P) (ζ : MultiVector P n), IsOpen U → ∃ X : GeometricCurrentOn U n, (∀ ω : TestFormOn U n, X ω = ζ ((ω : DifferentialForm (Euclid P) n) p)) ∧ X.support ⊆ {p}`

## Sibling prerequisites

- None.

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
