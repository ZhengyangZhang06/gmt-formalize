# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.dimension_reduction_results-a1.integer_density_tangent_planes-a1.two_dim_cone_density-a1.density_locally_constant-a1.light_disc-a1.arc_point_bounds-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-dimension-reduction-results-a1-integer-density-tangent-planes-a1-541cde9c3f/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.dimension_reduction_results-a1.integer_density_tangent_planes-a1.two_dim_cone_density-a1.density_locally_constant-a1.light_disc-a1`
- Child key: `arc_point_bounds`
- Declaration: `Submission.idtp_tdc_dlc_ld_arc_point_bounds`
- Exact Lean type: `∀ (P : ℕ) (z e : Euclid P) (φ : ℝ), ‖z‖ = 1 → ‖e‖ = 1 → inner ℝ z e = 0 → 0 ≤ φ → ‖Real.cos φ • z + Real.sin φ • e‖ = 1 ∧ ‖Real.cos φ • z + Real.sin φ • e - z‖ ≤ φ`

## Sibling prerequisites

- None.

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
