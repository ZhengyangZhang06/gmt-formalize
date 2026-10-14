# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.density_one_implies_regular-a1.epsilon_regularity-a1.graph_cycle_regular-a1.graph_orientation_jacobian-a1.continuous_covector_eval-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-density-one-implies-regular-a1-epsilon-regularity-a1-graph-cycle-ea8963379b/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.density_one_implies_regular-a1.epsilon_regularity-a1.graph_cycle_regular-a1.graph_orientation_jacobian-a1`
- Child key: `continuous_covector_eval`
- Declaration: `Submission.dgoj_exists_continuous_covector_eval`
- Exact Lean type: `∀ (P n : ℕ), ∃ ev : (Fin n → Euclid P) → MultiVector P n, Continuous ev ∧ ∀ (c : Fin n → Euclid P) (α : Covector (Euclid P) n), ev c α = α c`

## Sibling prerequisites

- None.

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
