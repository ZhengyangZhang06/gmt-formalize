# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.dimension_reduction_results-a1.codimension_one_regularity-a1.simons_regular_cone-a1.area_comparison-a1.submanifold_approx_tangent-a1.chart_localization-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-dimension-reduction-results-a1-codimension-one-regularity-a1-sim-e7608b0d7c/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.dimension_reduction_results-a1.codimension_one_regularity-a1.simons_regular_cone-a1.area_comparison-a1.submanifold_approx_tangent-a1`
- Child key: `chart_localization`
- Declaration: `Submission.codim1_ac_sat_chart_localization`
- Exact Lean type: `∀ (P m : ℕ) (N W W₀ : Set (Euclid P)) (V : Set (Euclid m)) (ψ : Euclid m → Euclid P) (v₀ : Euclid m) (ρ : ℝ), IsOpen W → IsOpen W₀ → ContinuousOn ψ V → InjOn ψ V → ψ '' V = W₀ ∩ N → (∀ K ⊆ W₀, IsCompact K → IsCompact (V ∩ ψ ⁻¹' K)) → v₀ ∈ V → ψ v₀ ∈ W → 0 < ρ → ball v₀ ρ ⊆ V → ∃ δ : ℝ, 0 < δ ∧ N ∩ W ∩ ball (ψ v₀) δ = ψ '' ball v₀ ρ ∩ ball (ψ v₀) δ`

## Sibling prerequisites

- `root.density_one_implies_regular-a1.mean_curvature_monotonicity-a1.chart_tangent_space-a1.inverse_continuity-a1`

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
