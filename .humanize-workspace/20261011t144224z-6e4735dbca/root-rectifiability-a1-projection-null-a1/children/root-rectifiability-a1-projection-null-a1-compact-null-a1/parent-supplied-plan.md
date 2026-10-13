# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.rectifiability-a1.projection_null-a1.compact_null-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/nodes/root-rectifiability-a1-projection-null-a1-compact-null-a1/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.rectifiability-a1.projection_null-a1`
- Child key: `compact_null`
- Declaration: `Submission.rpn_compact_null_of_le_mul_diff`
- Exact Lean type: `∀ (P : ℕ) (U K : Set (Eucl P)) (μ : Measure (Eucl P)) (C : ℝ≥0), IsOpen U → IsCompact K → K ⊆ U → (∀ W, CompactlyContainedOpen W U → μ W < ∞) → (∀ W, CompactlyContainedOpen W U → μ W ≤ (C : ℝ≥0∞) * μ (W \ K)) → μ K = 0`

## Sibling prerequisites

- None.

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
