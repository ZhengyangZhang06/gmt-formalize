# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.stationary_results-a1.stationary_mean_zero-a1.local_compact_ball-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T141923Z-ed98166de3/nodes/root-stationary-results-a1-stationary-mean-zero-a1-local-compact-ball-a1/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.stationary_results-a1.stationary_mean_zero-a1`
- Child key: `local_compact_ball`
- Declaration: `Submission.simon_submanifold_exists_closedBall_isCompact_inter`
- Exact Lean type: `∀ (n N : ℕ) (r : ℕ∞) (M : Set (Rn N)), Chapter02.IsSimonSubmanifold (E := Rn n) r M → ∀ y ∈ M, ∀ O : Set (Rn N), IsOpen O → y ∈ O → ∃ ρ : ℝ, 0 < ρ ∧ closedBall y ρ ⊆ O ∧ IsCompact (M ∩ closedBall y ρ)`

## Sibling prerequisites

- None.

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
