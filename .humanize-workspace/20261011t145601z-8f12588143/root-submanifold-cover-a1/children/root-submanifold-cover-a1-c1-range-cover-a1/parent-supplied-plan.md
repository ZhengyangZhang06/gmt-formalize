# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.submanifold_cover-a1.c1_range_cover-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T145601Z-8f12588143/nodes/root-submanifold-cover-a1-c1-range-cover-a1/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.submanifold_cover-a1`
- Child key: `c1_range_cover`
- Declaration: `Submission.c1_range_null_union_submanifolds`
- Exact Lean type: `∀ (n p : ℕ) (G : Rn n → Rn p), ContDiff ℝ 1 G → ∃ (N₀ : Set (Rn p)) (N : ℕ → Set (Rn p)), μHE[n] N₀ = 0 ∧ (∀ k, IsC1Submanifold n (N k)) ∧ Set.range G ⊆ N₀ ∪ ⋃ k, N k`

## Sibling prerequisites

- `root.submanifold_cover-a1.regular_ball_submanifold-a1`

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
