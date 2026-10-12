# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.density_one_implies_regular-a1.epsilon_regularity-a1.allard_graph-a1.harmonic_approximation-a1.interior_estimates-a1.mean_value_gradient_bound-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-density-one-implies-regular-a1-epsilon-regularity-a1-allard-grap-1805fa887c/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.density_one_implies_regular-a1.epsilon_regularity-a1.allard_graph-a1.harmonic_approximation-a1.interior_estimates-a1`
- Child key: `mean_value_gradient_bound`
- Declaration: `Submission.dorag_ha_ie_opNorm_sq_mul_volume_le_of_mean_value`
- Exact Lean type: `∀ (n : ℕ) (g : Euclid n → (Euclid n →L[ℝ] ℝ)) (y : Euclid n) (ρ : ℝ), 0 < ρ → ContinuousOn g (closedBall y ρ) → (∀ e : Euclid n, ∫ z in ball y ρ, g z e = (volume (ball y ρ)).toReal * g y e) → ‖g y‖ ^ 2 * (volume (ball y ρ)).toReal ≤ ∫ z in ball y ρ, ‖g z‖ ^ 2`

## Sibling prerequisites

- `root.density_one_implies_regular-a1.epsilon_regularity-a1.allard_graph-a1.harmonic_approximation-a1.interior_estimates-a1.mean_value_sq_bound-a1`

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
