# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.density_one_implies_regular-a1.epsilon_regularity-a1.allard_graph-a1.harmonic_approximation-a1.interior_estimates-a1.mean_value_derivative_bound-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-density-one-implies-regular-a1-epsilon-regularity-a1-allard-grap-b17a58928f/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.density_one_implies_regular-a1.epsilon_regularity-a1.allard_graph-a1.harmonic_approximation-a1.interior_estimates-a1`
- Child key: `mean_value_derivative_bound`
- Declaration: `Submission.dorag_ha_ie_norm_fderiv_le_of_mean_value`
- Exact Lean type: `∀ (n : ℕ) (u : Euclid n → ℝ) (x : Euclid n) (ρ K : ℝ), 0 < n → 0 < ρ → DifferentiableAt ℝ u x → ContinuousOn u (closedBall x (3 * ρ / 2)) → (∀ z ∈ closedBall x (3 * ρ / 2), |u z| ≤ K) → (∀ z ∈ closedBall x (ρ / 2), ∫ y in ball z ρ, u y = (volume (ball z ρ)).toReal * u z) → ‖fderiv ℝ u x‖ ≤ 2 * (n : ℝ) * K / ρ`

## Sibling prerequisites

- `root.density_one_implies_regular-a1.epsilon_regularity-a1.allard_graph-a1.harmonic_approximation-a1.interior_estimates-a1.shifted_ball_comparison-a1`

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
