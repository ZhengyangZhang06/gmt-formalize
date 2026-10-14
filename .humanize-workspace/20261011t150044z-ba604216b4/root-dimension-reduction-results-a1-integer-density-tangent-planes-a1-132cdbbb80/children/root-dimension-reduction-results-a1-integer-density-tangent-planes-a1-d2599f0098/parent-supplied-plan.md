# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.dimension_reduction_results-a1.integer_density_tangent_planes-a1.cone_sector_endpoint_density-a1.alpha_homogeneous-a1.slice_ae_const-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-dimension-reduction-results-a1-integer-density-tangent-planes-a1-d2599f0098/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.dimension_reduction_results-a1.integer_density_tangent_planes-a1.cone_sector_endpoint_density-a1.alpha_homogeneous-a1`
- Child key: `slice_ae_const`
- Declaration: `Submission.idtp_cse_ah_slice_ae_const`
- Exact Lean type: `∀ (a b c d : ℝ) (H : ℝ × ℝ → ℝ), c < d → IntegrableOn H (Ioo a b ×ˢ Ioo c d) → (∀ ψ l : ℝ → ℝ, ContDiff ℝ 1 ψ → ContDiff ℝ 1 l → tsupport ψ ⊆ Ioo c d → tsupport l ⊆ Ioo a b → ∫ p : ℝ × ℝ, deriv ψ p.2 * l p.1 * H p = 0) → ∀ᵐ t, t ∈ Ioo a b → ∃ k : ℝ, ∀ᵐ α, α ∈ Ioo c d → H (t, α) = k`

## Sibling prerequisites

- `root.dimension_reduction_results-a1.integer_density_tangent_planes-a1.cone_sector_endpoint_density-a1.alpha_homogeneous-a1.normalized_bump-a1`
- `root.dimension_reduction_results-a1.integer_density_tangent_planes-a1.cone_sector_endpoint_density-a1.alpha_homogeneous-a1.antiderivative_test-a1`
- `root.dimension_reduction_results-a1.integer_density_tangent_planes-a1.cone_sector_endpoint_density-a1.alpha_homogeneous-a1.slice_integral_ae_zero-a1`
- `root.dimension_reduction_results-a1.integer_density_tangent_planes-a1.cone_sector_endpoint_density-a1.alpha_homogeneous-a1.countable_separating_tests-a1`

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
