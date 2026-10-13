# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.flat_iff_weak-a1.total_boundedness-a1.top_dim_approx-a1.integer_median-a1.mean_deviation-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/nodes/root-flat-iff-weak-a1-total-boundedness-a1-top-dim-approx-a1-integer-51896063c1/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.flat_iff_weak-a1.total_boundedness-a1.top_dim_approx-a1.integer_median-a1`
- Child key: `mean_deviation`
- Declaration: `Submission.fiw_tb_tda_im_mean_deviation`
- Exact Lean type: `∀ {α : Type} [MeasurableSpace α] (μ : Measure α) (F : Set α) (a : ℝ) (u : α → ℝ), MeasurableSet F → 0 < a → μ F = ENNReal.ofReal a → Measurable u → IntegrableOn u F μ → ∫⁻ x in F, ENNReal.ofReal |u x - a⁻¹ * ∫ y in F, u y ∂μ| ∂μ ≤ ENNReal.ofReal a⁻¹ * ∫⁻ x in F, ∫⁻ y in F, ENNReal.ofReal |u x - u y| ∂μ ∂μ`

## Sibling prerequisites

- None.

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
