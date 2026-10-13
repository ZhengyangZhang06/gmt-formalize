# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.integral_compactness-a1.canonical_representation-a1.null_transfer-a1.open_subset_measure_lt-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T141839Z-af4f31741f/nodes/root-integral-compactness-a1-canonical-representation-a1-null-transfe-0a508a24e2/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.integral_compactness-a1.canonical_representation-a1.null_transfer-a1`
- Child key: `open_subset_measure_lt`
- Declaration: `Submission.intcpt_canon_nt_exists_open_subset_measure_lt`
- Exact Lean type: `∀ (N : ℕ) (μ : Measure (Euclidean N)) (W A : Set (Euclidean N)) (ε : ℝ≥0∞), IsOpen W → μ W ≠ ∞ → A ⊆ W → μ A < ε → ∃ O : Set (Euclidean N), IsOpen O ∧ A ⊆ O ∧ O ⊆ W ∧ μ O < ε`

## Sibling prerequisites

- None.

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
