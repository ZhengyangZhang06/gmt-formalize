# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.weighted_monotonicity-a1.cutoff_limit-a1.cutoff_seq-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T142930Z-d646011318/nodes/root-weighted-monotonicity-a1-cutoff-limit-a1-cutoff-seq-a1/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.weighted_monotonicity-a1.cutoff_limit-a1`
- Child key: `cutoff_seq`
- Declaration: `Submission.weighted_mono_cutoff_seq_exists`
- Exact Lean type: `∀ (a : ℝ), 0 < a → ∃ (φ : ℕ → ℝ → ℝ) (ε : ℕ → ℝ), Tendsto ε atTop (𝓝 0) ∧ ∀ m, 0 < ε m ∧ ε m < a ∧ ContDiff ℝ 1 (φ m) ∧ Antitone (φ m) ∧ (∀ t, t ≤ 1 → φ m t = 1) ∧ (∀ t, 1 + ε m ≤ t → φ m t = 0) ∧ (∀ t, 0 ≤ φ m t ∧ φ m t ≤ 1)`

## Sibling prerequisites

- None.

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
