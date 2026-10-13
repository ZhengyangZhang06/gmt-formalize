# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.dimension_reduction_results-a1.integer_density_tangent_planes-a1.cone_constant_density_planar-a1.stationary_cone_sheet_planar-a1.cone_chart-a1.plane_orthonormal-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-dimension-reduction-results-a1-integer-density-tangent-planes-a1-d02ceb54be/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.dimension_reduction_results-a1.integer_density_tangent_planes-a1.cone_constant_density_planar-a1.stationary_cone_sheet_planar-a1.cone_chart-a1`
- Child key: `plane_orthonormal`
- Declaration: `Submission.idtp_ccd_scsp_cc_plane_orthonormal`
- Exact Lean type: `∀ (P : ℕ) (Q : Submodule ℝ (Euclid P)) (u : Euclid P), Module.finrank ℝ Q = 2 → u ∈ Q → ‖u‖ = 1 → ∃ e : Euclid P, e ∈ Q ∧ ‖e‖ = 1 ∧ inner ℝ u e = 0 ∧ ∀ v ∈ Q, v = inner ℝ v u • u + inner ℝ v e • e`

## Sibling prerequisites

- None.

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
