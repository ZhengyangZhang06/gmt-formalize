# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.flat_iff_weak-a1.total_boundedness-a1.top_dim_approx-a1.integer_median-a1.median_exists-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/nodes/root-flat-iff-weak-a1-total-boundedness-a1-top-dim-approx-a1-integer-299420ad5d/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.flat_iff_weak-a1.total_boundedness-a1.top_dim_approx-a1.integer_median-a1`
- Child key: `median_exists`
- Declaration: `Submission.fiw_tb_tda_im_median_exists`
- Exact Lean type: `∀ {α : Type} [MeasurableSpace α] (μ : Measure α) (F : Set α) (a : ℝ) (u : α → ℝ), MeasurableSet F → 0 < a → μ F = ENNReal.ofReal a → Measurable u → (∀ x, ∃ k : ℤ, u x = k) → ∃ β : ℤ, ENNReal.ofReal (a / 2) ≤ μ (F ∩ {x | u x ≤ β}) ∧ ENNReal.ofReal (a / 2) ≤ μ (F ∩ {x | (β : ℝ) ≤ u x})`

## Sibling prerequisites

- None.

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
