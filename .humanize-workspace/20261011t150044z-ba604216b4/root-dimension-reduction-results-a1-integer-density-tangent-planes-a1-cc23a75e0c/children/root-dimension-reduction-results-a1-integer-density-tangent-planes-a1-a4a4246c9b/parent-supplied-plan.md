# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.dimension_reduction_results-a1.integer_density_tangent_planes-a1.flat_off_null_set-a1.one_dim_cones-a1.ray_orientation-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-dimension-reduction-results-a1-integer-density-tangent-planes-a1-a4a4246c9b/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.dimension_reduction_results-a1.integer_density_tangent_planes-a1.flat_off_null_set-a1.one_dim_cones-a1`
- Child key: `ray_orientation`
- Declaration: `Submission.idtp_fons_odc_ray_orientation`
- Exact Lean type: `∀ (P : ℕ) (R : IMRep (univ : Set (Euclid P)) 1) (F : Finset (Euclid P)), (∀ e ∈ F, ‖e‖ = 1) → (μHE[1] : Measure (Euclid P)) (R.carrier ∩ (⋃ e ∈ F, (fun t : ℝ => t • e) '' Ioi 0)ᶜ) = 0 → ∀ e ∈ F, ∀ᵐ x ∂((μHE[1] : Measure (Euclid P)).restrict (R.carrier ∩ (fun t : ℝ => t • e) '' Ioi 0)), R.orient x = ContinuousAlternatingMap.apply ℝ (Euclid P) ℝ (fun _ : Fin 1 => e) ∨ R.orient x = -ContinuousAlternatingMap.apply ℝ (Euclid P) ℝ (fun _ : Fin 1 => e)`

## Sibling prerequisites

- `root.dimension_reduction_results-a1.integer_density_tangent_planes-a1.flat_off_null_set-a1.one_dim_cones-a1.line_param-a1`

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
