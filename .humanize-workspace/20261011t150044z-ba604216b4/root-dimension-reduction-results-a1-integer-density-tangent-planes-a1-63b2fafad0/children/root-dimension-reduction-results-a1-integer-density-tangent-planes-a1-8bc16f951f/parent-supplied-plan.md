# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.dimension_reduction_results-a1.integer_density_tangent_planes-a1.cone_sector_endpoint_density-a1.alpha_homogeneous-a1.countable_separating_tests-a1.ae_zero_of_rat_intervals-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-dimension-reduction-results-a1-integer-density-tangent-planes-a1-8bc16f951f/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.dimension_reduction_results-a1.integer_density_tangent_planes-a1.cone_sector_endpoint_density-a1.alpha_homogeneous-a1.countable_separating_tests-a1`
- Child key: `ae_zero_of_rat_intervals`
- Declaration: `Submission.idtp_cse_ah_cst_ae_zero_of_rat_intervals`
- Exact Lean type: `∀ (c d : ℝ) (w : ℝ → ℝ), IntegrableOn w (Ioo c d) → (∀ p q : ℚ, c < (p : ℝ) → (p : ℝ) < (q : ℝ) → (q : ℝ) < d → ∫ α in Ioo (p : ℝ) (q : ℝ), w α = 0) → ∀ᵐ α, α ∈ Ioo c d → w α = 0`

## Sibling prerequisites

- None.

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
