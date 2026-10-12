# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.stationary_results-a1.chart_divergence-a1.chart_divergence_trace-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T141923Z-ed98166de3/nodes/root-stationary-results-a1-chart-divergence-a1-chart-divergence-trace-a1/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.stationary_results-a1.chart_divergence-a1`
- Child key: `chart_divergence_trace`
- Declaration: `Submission.chart_tangentialDivergence_eq_gram_trace`
- Exact Lean type: `∀ (n N : ℕ) (M : Set (Rn N)) (y : Rn N) (A : Rn n →L[ℝ] Rn N) (Y : Rn N → Rn N), Function.Injective A → tangentSpace M y = LinearMap.range A.toLinearMap → tangentialDivergence M Y y = LinearMap.trace ℝ (Rn n) (Ring.inverse (ContinuousLinearMap.adjoint A ∘L A) ∘L ContinuousLinearMap.adjoint A ∘L fderiv ℝ Y y ∘L A).toLinearMap`

## Sibling prerequisites

- `root.stationary_results-a1.chart_divergence-a1.gram_projection-a1`

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
