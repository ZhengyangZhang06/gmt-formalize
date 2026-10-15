# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.dimension_reduction_results-a1.moving_blowups-a1.closure_and_boundary_rectifiability-a1.cycle_im-a1.good_points-a1.density_comparison-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-dimension-reduction-results-a1-moving-blowups-a1-closure-and-bou-2130041a8d/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.dimension_reduction_results-a1.moving_blowups-a1.closure_and_boundary_rectifiability-a1.cycle_im-a1.good_points-a1`
- Child key: `density_comparison`
- Declaration: `Submission.dmcbr_ci_gp_density_comparison`
- Exact Lean type: `∀ (P n : ℕ) (μ : Measure (Euclid P)) (A : Set (Euclid P)) (t : ℝ≥0∞), (μHE[n] : Measure (Euclid P)) ≤ (unitBallVolume n / 2 ^ n) • (μH[(n : ℝ)] : Measure (Euclid P)) → 0 < t → (∀ x ∈ A, t < limsup (fun r : ℝ => μ (closedBall x r) / (unitBallVolume n * ENNReal.ofReal (r ^ n))) (𝓝[>] 0)) → t * μHE[n] A ≤ μ univ`

## Sibling prerequisites

- None.

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
