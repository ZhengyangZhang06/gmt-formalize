# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.dimension_reduction_results-a1.codimension_one_regularity-a1.simons_regular_cone-a1.area_comparison-a1.submanifold_approx_tangent-a1.chart_ball_tangent-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-dimension-reduction-results-a1-codimension-one-regularity-a1-sim-2f0652113f/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.dimension_reduction_results-a1.codimension_one_regularity-a1.simons_regular_cone-a1.area_comparison-a1.submanifold_approx_tangent-a1`
- Child key: `chart_ball_tangent`
- Declaration: `Submission.codim1_ac_sat_chart_ball_approxTangent`
- Exact Lean type: `∀ (P m : ℕ) (V : Set (Euclid m)) (ψ : Euclid m → Euclid P) (v₀ : Euclid m), IsOpen V → ContDiffOn ℝ 1 ψ V → v₀ ∈ V → Injective (fderiv ℝ ψ v₀) → ∃ ρ : ℝ, 0 < ρ ∧ ball v₀ ρ ⊆ V ∧ HasApproximateTangentSpaceAt m (ψ '' ball v₀ ρ) (ψ v₀) (LinearMap.range (fderiv ℝ ψ v₀ : Euclid m →ₗ[ℝ] Euclid P))`

## Sibling prerequisites

- `root.dimension_reduction_results-a1.codimension_one_regularity-a1.simons_regular_cone-a1.area_comparison-a1.submanifold_approx_tangent-a1.c1_local_extension-a1`
- `root.dimension_reduction_results-a1.codimension_one_regularity-a1.region_density_one-a1.rectifiable_density_one-a1.c1_cover-a1.local_lower_lipschitz-a1`
- `root.dimension_reduction_results-a1.codimension_one_regularity-a1.region_density_one-a1.rectifiable_density_one-a1.c1_piece_tangent-a1`

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
