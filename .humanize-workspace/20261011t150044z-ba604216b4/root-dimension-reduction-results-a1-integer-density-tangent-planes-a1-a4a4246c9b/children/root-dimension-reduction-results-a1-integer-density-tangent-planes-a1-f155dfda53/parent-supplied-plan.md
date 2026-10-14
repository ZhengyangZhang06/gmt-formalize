# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.dimension_reduction_results-a1.integer_density_tangent_planes-a1.flat_off_null_set-a1.one_dim_cones-a1.ray_orientation-a1.ray_isolation-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-dimension-reduction-results-a1-integer-density-tangent-planes-a1-f155dfda53/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.dimension_reduction_results-a1.integer_density_tangent_planes-a1.flat_off_null_set-a1.one_dim_cones-a1.ray_orientation-a1`
- Child key: `ray_isolation`
- Declaration: `Submission.idtp_fons_odc_ro_ray_isolation`
- Exact Lean type: `∀ (P : ℕ) (F : Finset (Euclid P)) (e : Euclid P) (t₀ : ℝ), (∀ e' ∈ F, ‖e'‖ = 1) → ‖e‖ = 1 → 0 < t₀ → ∃ δ : ℝ, 0 < δ ∧ ball (t₀ • e) δ ∩ (⋃ e' ∈ F, (fun t : ℝ => t • e') '' Ioi 0) ⊆ (fun t : ℝ => t • e) '' Ioi 0`

## Sibling prerequisites

- None.

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
