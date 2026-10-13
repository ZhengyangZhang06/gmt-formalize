# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.dimension_reduction_results-a1.integer_density_tangent_planes-a1.two_dim_cone_density-a1.density_locally_constant-a1.light_disc-a1.unit_vector_angle-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-dimension-reduction-results-a1-integer-density-tangent-planes-a1-721ca76048/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.dimension_reduction_results-a1.integer_density_tangent_planes-a1.two_dim_cone_density-a1.density_locally_constant-a1.light_disc-a1`
- Child key: `unit_vector_angle`
- Declaration: `Submission.idtp_tdc_dlc_ld_unit_vector_angle`
- Exact Lean type: `∀ (P : ℕ) (z e w : Euclid P) (L : ℝ), ‖z‖ = 1 → ‖e‖ = 1 → inner ℝ z e = 0 → ‖w‖ = 1 → w = inner ℝ w z • z + inner ℝ w e • e → ‖w - z‖ < L / 2 → ∃ (θ : ℝ) (v : Euclid P), 0 ≤ θ ∧ θ < L ∧ (v = e ∨ v = -e) ∧ w = Real.cos θ • z + Real.sin θ • v`

## Sibling prerequisites

- None.

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
