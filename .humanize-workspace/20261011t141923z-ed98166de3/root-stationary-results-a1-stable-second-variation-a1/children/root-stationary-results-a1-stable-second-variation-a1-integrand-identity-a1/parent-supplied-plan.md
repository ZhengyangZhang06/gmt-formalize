# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.stationary_results-a1.stable_second_variation-a1.integrand_identity-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T141923Z-ed98166de3/nodes/root-stationary-results-a1-stable-second-variation-a1-integrand-identity-a1/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.stationary_results-a1.stable_second_variation-a1`
- Child key: `integrand_identity`
- Declaration: `Submission.second_variation_integrand_eq_div_accel_add_stable`
- Exact Lean type: `∀ (N : ℕ) (M : Set (Rn N)) (φ : ℝ → Rn N → Rn N) (y : Rn N), (∀ τ ∈ tangentSpace M y, ∀ η ∈ tangentSpace M y, secondFundamentalForm M y τ η = secondFundamentalForm M y η τ) → (∀ τ ∈ tangentSpace M y, ∀ η ∈ tangentSpace M y, inner ℝ η (fderiv ℝ (initialVelocity φ) y τ) = -inner ℝ (initialVelocity φ y) (secondFundamentalForm M y τ η)) → inner ℝ (initialVelocity φ y) (meanCurvature M y) = 0 → secondVariationIntegrand M φ y = tangentialDivergence M (initialAcceleration φ) y + stableSecondVariationIntegrand M φ y`

## Sibling prerequisites

- None.

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
