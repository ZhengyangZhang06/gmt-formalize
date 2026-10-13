# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.dimension_reduction_results-a1.integer_density_tangent_planes-a1.cone_sector_endpoint_density-a1.alpha_homogeneous-a1.ae_eq_slice_average-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-dimension-reduction-results-a1-integer-density-tangent-planes-a1-1d6ccb1a71/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.dimension_reduction_results-a1.integer_density_tangent_planes-a1.cone_sector_endpoint_density-a1.alpha_homogeneous-a1`
- Child key: `ae_eq_slice_average`
- Declaration: `Submission.idtp_cse_ah_ae_eq_slice_average`
- Exact Lean type: `∀ (a b c d : ℝ) (H : ℝ × ℝ → ℝ), c < d → IntegrableOn H (Ioo a b ×ˢ Ioo c d) → (∀ᵐ t, t ∈ Ioo a b → ∃ k : ℝ, ∀ᵐ α, α ∈ Ioo c d → H (t, α) = k) → ∀ᵐ p : ℝ × ℝ, p ∈ Ioo a b ×ˢ Ioo c d → H p = (d - c)⁻¹ * ∫ α in Ioo c d, H (p.1, α)`

## Sibling prerequisites

- None.

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
