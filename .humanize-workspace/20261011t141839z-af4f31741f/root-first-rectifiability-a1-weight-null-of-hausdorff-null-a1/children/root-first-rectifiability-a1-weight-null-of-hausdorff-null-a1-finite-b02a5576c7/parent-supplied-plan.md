# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.first_rectifiability-a1.weight_null_of_hausdorff_null-a1.finite_density_ball_bound-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T141839Z-af4f31741f/nodes/root-first-rectifiability-a1-weight-null-of-hausdorff-null-a1-finite-b02a5576c7/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.first_rectifiability-a1.weight_null_of_hausdorff_null-a1`
- Child key: `finite_density_ball_bound`
- Declaration: `Submission.frt_ball_bound_of_finite_density`
- Exact Lean type: `∀ (N n : ℕ) (μ : Measure (Euclidean N)) (x : Euclidean N) (θ : ℝ≥0∞), θ ≠ ∞ → HasDensity n μ x θ → ∃ K j : ℕ, ∀ ρ : ℝ, 0 < ρ → ρ ≤ 1 / ((j : ℝ) + 1) → μ (closedBall x ρ) ≤ (K : ℝ≥0∞) * ENNReal.ofReal ρ ^ n`

## Sibling prerequisites

- None.

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
