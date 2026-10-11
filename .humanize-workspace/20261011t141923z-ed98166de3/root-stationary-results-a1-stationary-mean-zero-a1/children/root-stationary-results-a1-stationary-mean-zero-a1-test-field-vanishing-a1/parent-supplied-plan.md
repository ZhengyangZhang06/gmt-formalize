# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.stationary_results-a1.stationary_mean_zero-a1.test_field_vanishing-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T141923Z-ed98166de3/nodes/root-stationary-results-a1-stationary-mean-zero-a1-test-field-vanishing-a1/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.stationary_results-a1.stationary_mean_zero-a1`
- Child key: `test_field_vanishing`
- Declaration: `Submission.vector_field_eq_zero_of_integral_inner_test_fields`
- Exact Lean type: `∀ (N : ℕ) (μ : Measure (Rn N)) (M U : Set (Rn N)) (F : Rn N → Rn N), MeasurableSet M → IsOpen U → ContinuousOn F M → (∀ y ∈ M, ∀ O : Set (Rn N), IsOpen O → y ∈ O → 0 < μ (M ∩ O)) → (∀ y ∈ M, ∀ O : Set (Rn N), IsOpen O → y ∈ O → ∃ ρ : ℝ, 0 < ρ ∧ closedBall y ρ ⊆ O ∧ IsCompact (M ∩ closedBall y ρ)) → (∀ Y : Rn N → Rn N, ContDiff ℝ 2 Y → HasCompactSupport Y → tsupport Y ⊆ U → IsCompact (M ∩ tsupport Y) → IntegrableOn (fun y ↦ inner ℝ (Y y) (F y)) M μ ∧ ∫ y in M, inner ℝ (Y y) (F y) ∂μ = 0) → ∀ y ∈ M ∩ U, F y = 0`

## Sibling prerequisites

- None.

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
