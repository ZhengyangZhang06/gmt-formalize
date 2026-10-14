# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.integrality_weak_limits-a1.integer_density-a1.ae_blowup-a1.weighted_ball_growth-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/nodes/root-integrality-weak-limits-a1-integer-density-a1-ae-blowup-a1-weigh-e45cd9e0ed/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.integrality_weak_limits-a1.integer_density-a1.ae_blowup-a1`
- Child key: `weighted_ball_growth`
- Declaration: `Submission.ind_ab_weighted_ball_growth`
- Exact Lean type: `∀ (P n : ℕ) (M : Set (Eucl P)) (θ : Eucl P → ℝ) (x : Eucl P) (Q : Submodule ℝ (Eucl P)), NullMeasurableSet M (μHE[n] : Measure (Eucl P)) → (∀ y ∈ M, 0 ≤ θ y) → (∀ K : Set (Eucl P), IsCompact K → IntegrableOn θ (M ∩ K) (μHE[n] : Measure (Eucl P))) → HasWeightedApproximateTangentSpaceAt n M θ x Q → ∃ C : ℝ≥0, ∀ᶠ s in 𝓝[>] (0 : ℝ), ∫⁻ y in M ∩ closedBall x s, ENNReal.ofReal (θ y) ∂(μHE[n] : Measure (Eucl P)) ≤ C * ENNReal.ofReal (s ^ n)`

## Sibling prerequisites

- `root.integrality_weak_limits-a1.integer_density-a1.ae_blowup-a1.rescaled_tangent_limit-a1`

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
