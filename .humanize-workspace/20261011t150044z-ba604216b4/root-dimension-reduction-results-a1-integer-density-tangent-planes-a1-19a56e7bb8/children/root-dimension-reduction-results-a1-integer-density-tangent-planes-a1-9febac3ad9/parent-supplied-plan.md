# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.dimension_reduction_results-a1.integer_density_tangent_planes-a1.cone_constant_density_planar-a1.stationary_cone_sheet_planar-a1.test_field-a1.rotation_trace-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-dimension-reduction-results-a1-integer-density-tangent-planes-a1-9febac3ad9/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.dimension_reduction_results-a1.integer_density_tangent_planes-a1.cone_constant_density_planar-a1.stationary_cone_sheet_planar-a1.test_field-a1`
- Child key: `rotation_trace`
- Declaration: `Submission.idtp_ccd_scsp_tf_rotation_trace`
- Exact Lean type: `∀ (P : ℕ) (u e v w : Euclid P) (Q : Submodule ℝ (Euclid P)) (g : Euclid P → ℝ) (t : ℝ), Orthonormal ℝ ![v, w] → Submodule.span ℝ (Set.range ![v, w]) = Q → DifferentiableAt ℝ g (t • v) → LinearMap.trace ℝ (Euclid P) (Q.starProjection.toLinearMap ∘ₗ (fderiv ℝ (fun y : Euclid P => g y • (inner ℝ y u • e - inner ℝ y e • u)) (t • v)).toLinearMap) = fderiv ℝ g (t • v) w * (t * (inner ℝ v u * inner ℝ w e - inner ℝ v e * inner ℝ w u))`

## Sibling prerequisites

- `root.minimizing_implies_stationary-a1.first_variation_mass_bound-a1.trace_projection_frame-a1`

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
