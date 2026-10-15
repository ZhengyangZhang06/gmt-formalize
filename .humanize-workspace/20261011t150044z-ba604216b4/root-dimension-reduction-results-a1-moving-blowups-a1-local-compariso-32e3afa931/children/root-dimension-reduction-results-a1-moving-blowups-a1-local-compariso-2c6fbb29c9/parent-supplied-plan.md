# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.dimension_reduction_results-a1.moving_blowups-a1.local_comparison-a1.index_comparison-a1.cancel-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-dimension-reduction-results-a1-moving-blowups-a1-local-compariso-2c6fbb29c9/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.dimension_reduction_results-a1.moving_blowups-a1.local_comparison-a1.index_comparison-a1`
- Child key: `cancel`
- Declaration: `Submission.dimred_mbl_lc_ic_cancel`
- Exact Lean type: `∀ (a b s e M : ℝ≥0∞) (L : ℝ) (n : ℕ), 1 ≤ L → b ≤ M → M ≠ ∞ → a + b ≤ ENNReal.ofReal (L ^ n) * (s + e + e + b) → a ≤ ENNReal.ofReal (L ^ n) * (s + 2 * e) + ENNReal.ofReal (L ^ n - 1) * M`

## Sibling prerequisites

- None.

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
