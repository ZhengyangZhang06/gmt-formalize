# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.density_one_implies_regular-a1.epsilon_regularity-a1.allard_graph-a1.harmonic_approximation-a1.interior_estimates-a1.shifted_ball_comparison-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-density-one-implies-regular-a1-epsilon-regularity-a1-allard-grap-4463813c53/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.density_one_implies_regular-a1.epsilon_regularity-a1.allard_graph-a1.harmonic_approximation-a1.interior_estimates-a1`
- Child key: `shifted_ball_comparison`
- Declaration: `Submission.dorag_ha_ie_shifted_ball_integral_sub_le`
- Exact Lean type: `∀ (n : ℕ) (u : Euclid n → ℝ) (x w : Euclid n) (ρ K : ℝ), 0 < n → ‖w‖ ≤ ρ → 0 ≤ K → IntegrableOn u (ball x (ρ + ‖w‖)) → (∀ z ∈ ball x (ρ + ‖w‖), |u z| ≤ K) → |(∫ y in ball (x + w) ρ, u y) - ∫ y in ball x ρ, u y| ≤ K * (volume (ball (0 : Euclid n) 1)).toReal * ((ρ + ‖w‖) ^ n - (ρ - ‖w‖) ^ n)`

## Sibling prerequisites

- None.

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
