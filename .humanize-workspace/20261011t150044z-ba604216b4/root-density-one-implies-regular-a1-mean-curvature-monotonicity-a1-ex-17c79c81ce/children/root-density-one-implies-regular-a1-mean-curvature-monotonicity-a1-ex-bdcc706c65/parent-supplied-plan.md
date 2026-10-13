# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.density_one_implies_regular-a1.mean_curvature_monotonicity-a1.exp_monotonicity-a1.ode_monotonicity-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-density-one-implies-regular-a1-mean-curvature-monotonicity-a1-ex-bdcc706c65/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.density_one_implies_regular-a1.mean_curvature_monotonicity-a1.exp_monotonicity-a1`
- Child key: `ode_monotonicity`
- Declaration: `Submission.dsmc_em_exp_monotoneOn_of_deriv_ineq`
- Exact Lean type: `∀ (n : ℕ) (κ r : ℝ) (I I' : ℝ → ℝ), ContinuousOn I (Ioc 0 r) → (∀ s ∈ Ioo 0 r, HasDerivAt I (I' s) s) → (∀ s ∈ Ioo 0 r, (n : ℝ) * I s - s * I' s ≤ κ * s * I s) → MonotoneOn (fun s => Real.exp (κ * s) / s ^ n * I s) (Ioc 0 r)`

## Sibling prerequisites

- None.

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
