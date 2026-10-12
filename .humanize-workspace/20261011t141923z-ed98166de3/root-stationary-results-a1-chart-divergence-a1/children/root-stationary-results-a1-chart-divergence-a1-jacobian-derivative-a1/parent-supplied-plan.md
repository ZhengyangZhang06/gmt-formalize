# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.stationary_results-a1.chart_divergence-a1.jacobian_derivative-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T141923Z-ed98166de3/nodes/root-stationary-results-a1-chart-divergence-a1-jacobian-derivative-a1/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.stationary_results-a1.chart_divergence-a1`
- Child key: `jacobian_derivative`
- Declaration: `Submission.areaJacobianAt_contDiffOn_fderiv_eq_gram_trace`
- Exact Lean type: `∀ (n N : ℕ) (V : Set (Rn n)) (ψ : Rn n → Rn N), IsOpen V → ContDiffOn ℝ 2 ψ V → (∀ x ∈ V, Function.Injective (fderiv ℝ ψ x)) → ContDiffOn ℝ 1 (Chapter02.areaJacobianAt ψ) V ∧ ∀ x ∈ V, ∀ v : Rn n, fderiv ℝ (Chapter02.areaJacobianAt ψ) x v = Chapter02.areaJacobianAt ψ x * LinearMap.trace ℝ (Rn n) (Ring.inverse (ContinuousLinearMap.adjoint (fderiv ℝ ψ x) ∘L fderiv ℝ ψ x) ∘L ContinuousLinearMap.adjoint (fderiv ℝ ψ x) ∘L fderiv ℝ (fderiv ℝ ψ) x v).toLinearMap`

## Sibling prerequisites

- `root.stationary_results-a1.chart_divergence-a1.gram_projection-a1`
- `root.stationary_results-a1.chart_divergence-a1.det_jacobi-a1`

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
