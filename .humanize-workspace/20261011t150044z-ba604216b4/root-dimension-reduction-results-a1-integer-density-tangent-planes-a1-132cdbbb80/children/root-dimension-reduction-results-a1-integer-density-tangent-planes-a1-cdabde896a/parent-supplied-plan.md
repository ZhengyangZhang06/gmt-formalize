# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.dimension_reduction_results-a1.integer_density_tangent_planes-a1.cone_sector_endpoint_density-a1.alpha_homogeneous-a1.ae_linear_of_ae_scaling-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-dimension-reduction-results-a1-integer-density-tangent-planes-a1-cdabde896a/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.dimension_reduction_results-a1.integer_density_tangent_planes-a1.cone_sector_endpoint_density-a1.alpha_homogeneous-a1`
- Child key: `ae_linear_of_ae_scaling`
- Declaration: `Submission.idtp_cse_ah_ae_linear_of_ae_scaling`
- Exact Lean type: `∀ (s : ℝ) (h : ℝ → ℝ), 0 < s → s ≤ 1 → AEStronglyMeasurable h (volume.restrict (Ioo (1 - s) (1 + s))) → (∀ r : ℝ, |r - 1| < s / 4 → ∀ᵐ u, u ∈ Ioo (1 - s / 2) (1 + s / 2) → h (r * u) = r * h u) → ∃ c : ℝ, ∀ᵐ v, v ∈ Ioo (1 - s / 8) (1 + s / 8) → h v = c * v`

## Sibling prerequisites

- None.

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
