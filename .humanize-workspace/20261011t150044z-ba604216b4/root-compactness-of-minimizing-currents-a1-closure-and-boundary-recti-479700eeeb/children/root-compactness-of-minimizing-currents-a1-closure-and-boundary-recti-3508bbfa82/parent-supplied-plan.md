# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.compactness_of_minimizing_currents-a1.closure_and_boundary_rectifiability-a1.cycle_im-a1.good_points-a1.density_comparison-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-compactness-of-minimizing-currents-a1-closure-and-boundary-recti-3508bbfa82/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.compactness_of_minimizing_currents-a1.closure_and_boundary_rectifiability-a1.cycle_im-a1.good_points-a1`
- Child key: `density_comparison`
- Declaration: `Submission.cbr_ci_gp_density_comparison`
- Exact Lean type: `∀ (P n : ℕ) (μ : Measure (Euclid P)) (A : Set (Euclid P)) (t : ℝ≥0∞), (μHE[n] : Measure (Euclid P)) ≤ (unitBallVolume n / 2 ^ n) • (μH[(n : ℝ)] : Measure (Euclid P)) → 0 < t → (∀ x ∈ A, t < limsup (fun r : ℝ => μ (closedBall x r) / (unitBallVolume n * ENNReal.ofReal (r ^ n))) (𝓝[>] 0)) → t * μHE[n] A ≤ μ univ`

## Sibling prerequisites

- None.

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
