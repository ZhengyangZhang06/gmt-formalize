# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.dimension_reduction_results-a1.cone_splitting-a1.product_support_density-a1.ball_volume_slice-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-dimension-reduction-results-a1-cone-splitting-a1-product-support-cca8e1c728/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.dimension_reduction_results-a1.cone_splitting-a1.product_support_density-a1`
- Child key: `ball_volume_slice`
- Declaration: `Submission.dimred_cs_psd_ball_volume_slice`
- Exact Lean type: `∀ (d m : ℕ) (ρ : ℝ), 0 ≤ ρ → volume (ball (0 : Euclid (d + m)) ρ) = ∫⁻ σ : Euclid d, volume (ball (0 : Euclid m) (Real.sqrt (ρ ^ 2 - ‖σ‖ ^ 2)))`

## Sibling prerequisites

- None.

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
