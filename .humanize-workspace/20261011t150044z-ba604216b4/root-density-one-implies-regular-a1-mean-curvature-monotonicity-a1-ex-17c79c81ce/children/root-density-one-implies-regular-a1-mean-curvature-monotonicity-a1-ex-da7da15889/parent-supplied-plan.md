# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.density_one_implies_regular-a1.mean_curvature_monotonicity-a1.exp_monotonicity-a1.cutoff_ball_limit-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-density-one-implies-regular-a1-mean-curvature-monotonicity-a1-ex-da7da15889/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.density_one_implies_regular-a1.mean_curvature_monotonicity-a1.exp_monotonicity-a1`
- Child key: `cutoff_ball_limit`
- Declaration: `Submission.dsmc_em_cutoff_tendsto_ball`
- Exact Lean type: `∃ η : ℕ → ℝ → ℝ, (∀ j, ContDiff ℝ 1 (η j)) ∧ (∀ j u, 0 ≤ η j u) ∧ (∀ j u, deriv (η j) u ≤ 0) ∧ (∀ j u, 1 ≤ u → η j u = 0) ∧ ∀ (P : ℕ) (μ : Measure (Euclid P)) (z : Euclid P) (s : ℝ), 0 < s → μ (ball z s) < ∞ → Tendsto (fun j => ∫ x, η j (‖x - z‖ ^ 2 / s ^ 2) ∂μ) atTop (𝓝 (μ.real (ball z s)))`

## Sibling prerequisites

- None.

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
