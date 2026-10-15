# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.dimension_reduction_results-a1.integer_density_tangent_planes-a1.cone_sector_endpoint_density-a1.alpha_homogeneous-a1.product_integral_reduce-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-dimension-reduction-results-a1-integer-density-tangent-planes-a1-c79beab8a3/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.dimension_reduction_results-a1.integer_density_tangent_planes-a1.cone_sector_endpoint_density-a1.alpha_homogeneous-a1`
- Child key: `product_integral_reduce`
- Declaration: `Submission.idtp_cse_ah_product_integral_reduce`
- Exact Lean type: `∀ (a b c d : ℝ) (H : ℝ × ℝ → ℝ) (h f ψ₀ : ℝ → ℝ), (∀ᵐ p : ℝ × ℝ, p ∈ Ioo a b ×ˢ Ioo c d → H p = h p.1) → (∀ t, t ∉ Ioo a b → f t = 0) → (∀ α, α ∉ Ioo c d → ψ₀ α = 0) → ∫ α, ψ₀ α = 1 → ∫ p : ℝ × ℝ, f p.1 * ψ₀ p.2 * H p = ∫ t, f t * h t`

## Sibling prerequisites

- None.

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
