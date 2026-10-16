# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.dimension_reduction_results-a1.integer_density_tangent_planes-a1.cone_constant_density_planar-a1.stationary_cone_sheet_planar-a1.arc_planarity-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-dimension-reduction-results-a1-integer-density-tangent-planes-a1-c4fad9952f/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.dimension_reduction_results-a1.integer_density_tangent_planes-a1.cone_constant_density_planar-a1.stationary_cone_sheet_planar-a1`
- Child key: `arc_planarity`
- Declaration: `Submission.idtp_ccd_scsp_arc_planarity`
- Exact Lean type: `∀ (P : ℕ) (u e : Euclid P) (s : ℝ) (γ : ℝ → Euclid P), ‖u‖ = 1 → ‖e‖ = 1 → inner ℝ u e = 0 → ContDiffOn ℝ 1 γ (Ioo (-s) s) → (∀ α ∈ Ioo (-s) s, ‖γ α‖ = 1 ∧ 0 < inner ℝ (γ α) u ∧ Real.arctan (inner ℝ (γ α) e / inner ℝ (γ α) u) = α) → (∀ α ∈ Ioo (-s) s, ‖deriv γ α‖ = inner ℝ (γ α) u ^ 2 + inner ℝ (γ α) e ^ 2) → ∀ α ∈ Ioo (-s) s, γ α = Real.cos α • u + Real.sin α • e`

## Sibling prerequisites

- `root.dimension_reduction_results-a1.integer_density_tangent_planes-a1.cone_constant_density_planar-a1.stationary_cone_sheet_planar-a1.angle_curve-a1`

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
