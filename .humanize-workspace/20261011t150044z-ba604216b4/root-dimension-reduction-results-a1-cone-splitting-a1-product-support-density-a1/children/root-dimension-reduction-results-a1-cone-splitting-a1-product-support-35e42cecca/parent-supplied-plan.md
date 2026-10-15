# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.dimension_reduction_results-a1.cone_splitting-a1.product_support_density-a1.radial_support-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-dimension-reduction-results-a1-cone-splitting-a1-product-support-35e42cecca/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.dimension_reduction_results-a1.cone_splitting-a1.product_support_density-a1`
- Child key: `radial_support`
- Declaration: `Submission.dimred_cs_psd_radial_support`
- Exact Lean type: `∀ (d : ℕ) (f : ℝ → ℝ≥0∞), Monotone f → ((∀ ε : ℝ, 0 < ε → (∫⁻ σ : Euclid d, f (Real.sqrt (ε ^ 2 - ‖σ‖ ^ 2))) ≠ 0) ↔ ∀ ε : ℝ, 0 < ε → f ε ≠ 0)`

## Sibling prerequisites

- None.

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
