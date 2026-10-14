# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.dimension_reduction_results-a1.integer_density_tangent_planes-a1.cone_sector_endpoint_density-a1.alpha_homogeneous-a1.ae_scaling_of_weak_scaling-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-dimension-reduction-results-a1-integer-density-tangent-planes-a1-1fbc09489d/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.dimension_reduction_results-a1.integer_density_tangent_planes-a1.cone_sector_endpoint_density-a1.alpha_homogeneous-a1`
- Child key: `ae_scaling_of_weak_scaling`
- Declaration: `Submission.idtp_cse_ah_ae_scaling_of_weak_scaling`
- Exact Lean type: `∀ (a b r : ℝ) (h : ℝ → ℝ), 0 < r → IntegrableOn h (Ioo a b) → IntegrableOn h (Ioo (r * a) (r * b)) → (∀ l : ℝ → ℝ, ContDiff ℝ 1 l → tsupport l ⊆ Ioo a b → ∫ t, l (t / r) * h t = r ^ 2 * ∫ t, l t * h t) → ∀ᵐ u, u ∈ Ioo a b → h (r * u) = r * h u`

## Sibling prerequisites

- None.

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
