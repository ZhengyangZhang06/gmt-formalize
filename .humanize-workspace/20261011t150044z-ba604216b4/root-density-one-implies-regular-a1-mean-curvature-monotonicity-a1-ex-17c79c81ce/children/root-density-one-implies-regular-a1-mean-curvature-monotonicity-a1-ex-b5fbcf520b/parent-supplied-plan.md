# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.density_one_implies_regular-a1.mean_curvature_monotonicity-a1.exp_monotonicity-a1.cutoff_integral_derivative-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-density-one-implies-regular-a1-mean-curvature-monotonicity-a1-ex-b5fbcf520b/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.density_one_implies_regular-a1.mean_curvature_monotonicity-a1.exp_monotonicity-a1`
- Child key: `cutoff_integral_derivative`
- Declaration: `Submission.dsmc_em_cutoff_integral_hasDerivAt`
- Exact Lean type: `∀ (P : ℕ) (μ : Measure (Euclid P)) (z : Euclid P) (r : ℝ) (η : ℝ → ℝ), μ (ball z r) < ∞ → ContDiff ℝ 1 η → (∀ u, 1 ≤ u → η u = 0) → ContinuousOn (fun t => ∫ x, η (‖x - z‖ ^ 2 / t ^ 2) ∂μ) (Ioc 0 r) ∧ ∀ s ∈ Ioo 0 r, HasDerivAt (fun t => ∫ x, η (‖x - z‖ ^ 2 / t ^ 2) ∂μ) (-(∫ x, 2 * (‖x - z‖ ^ 2 / s ^ 2) * deriv η (‖x - z‖ ^ 2 / s ^ 2) ∂μ) / s) s`

## Sibling prerequisites

- None.

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
