# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.bv_results-a1.mollifier_gradient-a1.compact_exhaustion-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T141923Z-ed98166de3/nodes/root-bv-results-a1-mollifier-gradient-a1-compact-exhaustion-a1/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.bv_results-a1.mollifier_gradient-a1`
- Child key: `compact_exhaustion`
- Declaration: `Submission.bv_lintegral_open_le_of_compact`
- Exact Lean type: `∀ (n : ℕ) (O : Set (Rn n)) (f : Rn n → ℝ≥0∞) (M : ℝ≥0∞), IsOpen O → Measurable f → (∀ L, IsCompact L → L ⊆ O → ∫⁻ x in L, f x ≤ M) → ∫⁻ x in O, f x ≤ M`

## Sibling prerequisites

- None.

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
