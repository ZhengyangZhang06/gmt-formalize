# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.coarea_formula-a1.critical_fibers_euclidean-a1.ball_cover_count-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T141923Z-ed98166de3/nodes/root-coarea-formula-a1-critical-fibers-euclidean-a1-ball-cover-count-a1/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.coarea_formula-a1.critical_fibers_euclidean-a1`
- Child key: `ball_cover_count`
- Declaration: `Submission.bounded_set_closedBall_cover_card_mul_pow_le`
- Exact Lean type: `∀ (n : ℕ) (K : Set (Rn n)), Bornology.IsBounded K → ∃ C : ℝ, ∀ r : ℝ, 0 < r → r ≤ 1 → ∃ s : Finset (Rn n), (↑s : Set (Rn n)) ⊆ K ∧ K ⊆ ⋃ x ∈ s, closedBall x r ∧ (s.card : ℝ) * r ^ n ≤ C`

## Sibling prerequisites

- None.

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
