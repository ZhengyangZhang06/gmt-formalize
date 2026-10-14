# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.dimension_reduction_results-a1.regular_point_density-a1.near_isometric_chart-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-dimension-reduction-results-a1-regular-point-density-a1-near-iso-6af3c83f05/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.dimension_reduction_results-a1.regular_point_density-a1`
- Child key: `near_isometric_chart`
- Declaration: `Submission.dimred_rpd_near_isometric_chart`
- Exact Lean type: `∀ (P n : ℕ) (M : Set (Euclid P)) (z : Euclid P), IsEmbeddedSubmanifold 1 n M → z ∈ M → ∀ ε : ℝ, 0 < ε → ∃ (χ : Euclid n → Euclid P) (δ δ' : ℝ), 0 < δ ∧ 0 < δ' ∧ χ 0 = z ∧ (∀ a ∈ ball (0 : Euclid n) δ, ∀ b ∈ ball (0 : Euclid n) δ, (1 - ε) * ‖a - b‖ ≤ ‖χ a - χ b‖ ∧ ‖χ a - χ b‖ ≤ (1 + ε) * ‖a - b‖) ∧ χ '' ball 0 δ ⊆ M ∧ M ∩ ball z δ' ⊆ χ '' ball 0 δ`

## Sibling prerequisites

- `root.density_one_implies_regular-a1.mean_curvature_monotonicity-a1.chart_tangent_space-a1.inverse_continuity-a1`

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
