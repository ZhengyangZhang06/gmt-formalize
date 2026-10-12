# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.stationary_results-a1.divergence_identity-a1.chart_localization-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T141923Z-ed98166de3/nodes/root-stationary-results-a1-divergence-identity-a1-chart-localization-a1/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.stationary_results-a1.divergence_identity-a1`
- Child key: `chart_localization`
- Declaration: `Submission.chart_setIntegral_eq_zero_of_trace_fderiv_eq`
- Exact Lean type: `∀ (n N : ℕ) (r : ℕ∞) (M : Set (Rn N)) (V : Set (Rn n)) (W K : Set (Rn N)) (ψ : Rn n → Rn N) (g : Rn N → ℝ) (w : Rn n → Rn n), 1 ≤ r → Chapter02.IsSimonLocalRepresentation r M V W ψ → MeasurableSet M → IsCompact K → K ⊆ W → (∀ y ∈ M, y ∉ K → g y = 0) → ContDiffOn ℝ 1 w V → (∀ x ∈ V, ψ x ∉ K → w x = 0) → (∀ x ∈ V, LinearMap.trace ℝ (Rn n) (fderiv ℝ w x).toLinearMap = Chapter02.areaJacobianAt ψ x * g (ψ x)) → ∫ y in M, g y ∂μHE[n] = 0`

## Sibling prerequisites

- `root.stationary_results-a1.divergence_identity-a1.euclidean_divergence-a1`

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
