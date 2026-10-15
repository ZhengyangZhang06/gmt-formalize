# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.dimension_reduction_results-a1.monotonicity-a1.ae_density_lower_bound-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-dimension-reduction-results-a1-monotonicity-a1-ae-density-lower-bound-a1/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.dimension_reduction_results-a1.monotonicity-a1`
- Child key: `ae_density_lower_bound`
- Declaration: `Submission.dimred_mono_ae_ball_density_ge_one`
- Exact Lean type: `∀ (P n : ℕ) (U : Set (Euclid P)) (R : IMRep U n), IsOpen U → ∀ᵐ x ∂R.measure, ∀ θ : ℝ, Tendsto (fun ρ : ℝ => R.measure (ball x ρ) / (unitBallVolume n * ENNReal.ofReal (ρ ^ n))) (𝓝[>] 0) (𝓝 (ENNReal.ofReal θ)) → 1 ≤ θ`

## Sibling prerequisites

- `root.regular_set_dense-a1.density_eq_multiplicity-a1.unweighted_density_one-a1`
- `root.regular_set_dense-a1.density_eq_multiplicity-a1.closed_to_open_ball_density-a1`

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
