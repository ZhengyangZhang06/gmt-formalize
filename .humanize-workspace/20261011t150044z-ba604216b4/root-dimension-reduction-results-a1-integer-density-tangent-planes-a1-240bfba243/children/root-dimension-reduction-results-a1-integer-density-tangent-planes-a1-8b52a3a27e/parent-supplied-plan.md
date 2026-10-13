# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.dimension_reduction_results-a1.integer_density_tangent_planes-a1.cone_sector_endpoint_density-a1.box_mass_limits-a1.box_inclusions-a1.projection_residual-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-dimension-reduction-results-a1-integer-density-tangent-planes-a1-8b52a3a27e/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.dimension_reduction_results-a1.integer_density_tangent_planes-a1.cone_sector_endpoint_density-a1.box_mass_limits-a1.box_inclusions-a1`
- Child key: `projection_residual`
- Declaration: `Submission.idtp_cse_bml_rbi_projection_residual_le`
- Exact Lean type: `∀ (P : ℕ) (Q : Submodule ℝ (Euclid P)) (a w : Euclid P) (s' : ℝ), a ∈ Q → 0 ≤ s' → ‖(a + s' • w) - Q.starProjection (a + s' • w)‖ ≤ s' * ‖w‖`

## Sibling prerequisites

- None.

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
