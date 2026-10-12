# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.coarea_formula-a1.critical_fibers_euclidean-a1.ball_cover_count-a1.maximal_separated_cover-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T141923Z-ed98166de3/nodes/root-coarea-formula-a1-critical-fibers-euclidean-a1-ball-cover-count-37d623ba8d/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.coarea_formula-a1.critical_fibers_euclidean-a1.ball_cover_count-a1`
- Child key: `maximal_separated_cover`
- Declaration: `Submission.exists_separated_finset_subset_cover_closedBall`
- Exact Lean type: `∀ (X : Type) [PseudoMetricSpace X] (K : Set X) (r : ℝ) (N : ℕ), 0 ≤ r → (∀ F : Finset X, (↑F : Set X) ⊆ K → (∀ x ∈ F, ∀ y ∈ F, x ≠ y → r < dist x y) → F.card ≤ N) → ∃ F : Finset X, (↑F : Set X) ⊆ K ∧ (∀ x ∈ F, ∀ y ∈ F, x ≠ y → r < dist x y) ∧ K ⊆ ⋃ x ∈ F, closedBall x r`

## Sibling prerequisites

- None.

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
