# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.stationary_results-a1.stationary_mean_zero-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T141923Z-ed98166de3/nodes/root-stationary-results-a1-stationary-mean-zero-a1/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.stationary_results-a1`
- Child key: `stationary_mean_zero`
- Declaration: `Submission.stationary_imp_mean_curvature_zero`
- Exact Lean type: `((∀ (n N : ℕ) (r : ℕ∞) (M : Set (Rn N)) (V : Set (Rn n)) (W : Set (Rn N)) (ψ : Rn n → Rn N), 1 ≤ r → Chapter02.IsSimonLocalRepresentation r M V W ψ → ∀ x ∈ V, tangentSpace M (ψ x) = LinearMap.range (fderiv ℝ ψ x).toLinearMap) ∧ ∀ (n N : ℕ) (r : ℕ∞) (M : Set (Rn N)), Chapter02.IsSimonSubmanifold (E := Rn n) r M → MeasurableSet M ∧ ContinuousOn (tangentProjection M) M) → FirstVariation → ∀ (n ℓ : ℕ) (M U : Set (Rn (n + ℓ))), Chapter02.IsSimonSubmanifold (E := Rn n) 2 M → IsOpen U → IsStationaryIn n M U → ∀ y ∈ M ∩ U, meanCurvature M y = 0`

## Sibling prerequisites

- `root.stationary_results-a1.measure_bounds-a1`
- `root.stationary_results-a1.scaled_deformation-a1`
- `root.stationary_results-a1.sff_properties-a1`
- `root.stationary_results-a1.divergence_identity-a1`

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
