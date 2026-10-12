# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.stationary_results-a1.chart_divergence-a1.jacobian_derivative-a1.gram_derivative-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T141923Z-ed98166de3/nodes/root-stationary-results-a1-chart-divergence-a1-jacobian-derivative-a1-42df20fbf6/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.stationary_results-a1.chart_divergence-a1.jacobian_derivative-a1`
- Child key: `gram_derivative`
- Declaration: `Submission.adjoint_comp_fderiv_contDiffOn_fderiv_eq_add`
- Exact Lean type: `∀ (n N : ℕ) (V : Set (Rn n)) (ψ : Rn n → Rn N), IsOpen V → ContDiffOn ℝ 2 ψ V → ContDiffOn ℝ 1 (fun x ↦ ContinuousLinearMap.adjoint (fderiv ℝ ψ x) ∘L fderiv ℝ ψ x) V ∧ ∀ x ∈ V, ∀ v : Rn n, fderiv ℝ (fun x ↦ ContinuousLinearMap.adjoint (fderiv ℝ ψ x) ∘L fderiv ℝ ψ x) x v = ContinuousLinearMap.adjoint (fderiv ℝ ψ x) ∘L fderiv ℝ (fderiv ℝ ψ) x v + ContinuousLinearMap.adjoint (fderiv ℝ (fderiv ℝ ψ) x v) ∘L fderiv ℝ ψ x`

## Sibling prerequisites

- None.

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
