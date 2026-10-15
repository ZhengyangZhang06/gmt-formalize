# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.dimension_reduction_results-a1.integer_density_tangent_planes-a1.cone_constant_density_planar-a1.stationary_cone_sheet_planar-a1.local_inverse-a1.chart_image_open-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-dimension-reduction-results-a1-integer-density-tangent-planes-a1-d3639ee607/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.dimension_reduction_results-a1.integer_density_tangent_planes-a1.cone_constant_density_planar-a1.stationary_cone_sheet_planar-a1.local_inverse-a1`
- Child key: `chart_image_open`
- Declaration: `Submission.idtp_ccd_scsp_li_chart_image_open`
- Exact Lean type: `∀ (P d : ℕ) (M W : Set (Euclid P)) (V V₁ : Set (Euclid d)) (ψ : Euclid d → Euclid P), IsOpen W → ContinuousOn ψ V → InjOn ψ V → ψ '' V = W ∩ M → (∀ K ⊆ W, IsCompact K → IsCompact (V ∩ ψ ⁻¹' K)) → IsOpen V₁ → V₁ ⊆ V → ∃ N₀ : Set (Euclid P), IsOpen N₀ ∧ M ∩ N₀ = ψ '' V₁`

## Sibling prerequisites

- `root.density_one_implies_regular-a1.mean_curvature_monotonicity-a1.chart_tangent_space-a1.inverse_continuity-a1`

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
