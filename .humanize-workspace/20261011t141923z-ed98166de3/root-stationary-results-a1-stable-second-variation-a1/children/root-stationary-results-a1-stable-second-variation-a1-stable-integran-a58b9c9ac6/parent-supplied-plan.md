# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.stationary_results-a1.stable_second_variation-a1.stable_integrand_integrable-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T141923Z-ed98166de3/nodes/root-stationary-results-a1-stable-second-variation-a1-stable-integran-a58b9c9ac6/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.stationary_results-a1.stable_second_variation-a1`
- Child key: `stable_integrand_integrable`
- Declaration: `Submission.stable_second_variation_integrand_integrableOn`
- Exact Lean type: `∀ (n N : ℕ) (M K : Set (Rn N)) (φ : ℝ → Rn N → Rn N), MeasurableSet M → ContinuousOn (tangentProjection M) M → ContDiff ℝ 1 (initialVelocity φ) → IsClosed K → (∀ x ∉ K, initialVelocity φ x = 0) → IsCompact (M ∩ K) → μHE[n] (M ∩ K) < ⊤ → (∀ y ∈ M, ∀ τ ∈ tangentSpace M y, ∀ η ∈ tangentSpace M y, inner ℝ η (fderiv ℝ (initialVelocity φ) y τ) = -inner ℝ (initialVelocity φ y) (secondFundamentalForm M y τ η)) → (∀ y ∈ M, y ∉ K → stableSecondVariationIntegrand M φ y = 0) ∧ IntegrableOn (stableSecondVariationIntegrand M φ) M μHE[n]`

## Sibling prerequisites

- None.

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
