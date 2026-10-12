# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.stationary_results-a1.chart_divergence-a1.jacobian_derivative-a1.trace_swap-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T141923Z-ed98166de3/nodes/root-stationary-results-a1-chart-divergence-a1-jacobian-derivative-a1-8970b38ef5/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.stationary_results-a1.chart_divergence-a1.jacobian_derivative-a1`
- Child key: `trace_swap`
- Declaration: `Submission.trace_comp_adjoint_comp_swap_of_symm`
- Exact Lean type: `∀ (n N : ℕ) (A S : Rn n →L[ℝ] Rn N) (P : Rn n →L[ℝ] Rn n), (∀ v w : Rn n, inner ℝ (P v) w = inner ℝ v (P w)) → LinearMap.trace ℝ (Rn n) (P ∘L ContinuousLinearMap.adjoint S ∘L A).toLinearMap = LinearMap.trace ℝ (Rn n) (P ∘L ContinuousLinearMap.adjoint A ∘L S).toLinearMap`

## Sibling prerequisites

- None.

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
