# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.stationary_results-a1.stable_second_variation-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T141923Z-ed98166de3/nodes/root-stationary-results-a1-stable-second-variation-a1/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.stationary_results-a1`
- Child key: `stable_second_variation`
- Declaration: `Submission.second_variation_stationary_of_variations`
- Exact Lean type: `((∀ (n N : ℕ) (r : ℕ∞) (M : Set (Rn N)) (V : Set (Rn n)) (W : Set (Rn N)) (ψ : Rn n → Rn N), 1 ≤ r → Chapter02.IsSimonLocalRepresentation r M V W ψ → ∀ x ∈ V, tangentSpace M (ψ x) = LinearMap.range (fderiv ℝ ψ x).toLinearMap) ∧ ∀ (n N : ℕ) (r : ℕ∞) (M : Set (Rn N)), Chapter02.IsSimonSubmanifold (E := Rn n) r M → MeasurableSet M ∧ ContinuousOn (tangentProjection M) M) → FirstVariation → SecondVariation → SecondVariationStationary`

## Sibling prerequisites

- `root.stationary_results-a1.deformation_regularity-a1`
- `root.stationary_results-a1.sff_properties-a1`
- `root.stationary_results-a1.divergence_identity-a1`
- `root.stationary_results-a1.stationary_mean_zero-a1`

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
