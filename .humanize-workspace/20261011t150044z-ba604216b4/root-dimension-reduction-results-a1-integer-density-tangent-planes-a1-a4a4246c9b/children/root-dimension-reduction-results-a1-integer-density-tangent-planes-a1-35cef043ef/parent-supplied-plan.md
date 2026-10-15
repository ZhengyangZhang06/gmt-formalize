# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.dimension_reduction_results-a1.integer_density_tangent_planes-a1.flat_off_null_set-a1.one_dim_cones-a1.ray_orientation-a1.line_orientation-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-dimension-reduction-results-a1-integer-density-tangent-planes-a1-35cef043ef/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.dimension_reduction_results-a1.integer_density_tangent_planes-a1.flat_off_null_set-a1.one_dim_cones-a1.ray_orientation-a1`
- Child key: `line_orientation`
- Declaration: `Submission.idtp_fons_odc_ro_line_orientation`
- Exact Lean type: `∀ (P : ℕ) (e : Euclid P) (ξ : MultiVector P 1), ‖e‖ = 1 → IsUnitOrientationOf ξ (Submodule.span ℝ {e}) → ξ = ContinuousAlternatingMap.apply ℝ (Euclid P) ℝ (fun _ : Fin 1 => e) ∨ ξ = -ContinuousAlternatingMap.apply ℝ (Euclid P) ℝ (fun _ : Fin 1 => e)`

## Sibling prerequisites

- None.

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
