# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.submanifold_cover-a1.regular_ball_submanifold-a1.local_lower_bounds-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T145601Z-8f12588143/nodes/root-submanifold-cover-a1-regular-ball-submanifold-a1-local-lower-bounds-a1/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.submanifold_cover-a1.regular_ball_submanifold-a1`
- Child key: `local_lower_bounds`
- Declaration: `Submission.c1_injective_fderiv_local_lower_bounds`
- Exact Lean type: `∀ (n p : ℕ) (G : Rn n → Rn p) (U : Set (Rn n)), IsOpen U → ContDiffOn ℝ 1 G U → ∀ x ∈ U, Function.Injective (fderiv ℝ G x) → ∃ r : ℝ, 0 < r ∧ Metric.closedBall x r ⊆ U ∧ ∃ c : ℝ, 0 < c ∧ (∀ z ∈ Metric.closedBall x r, ∀ z' ∈ Metric.closedBall x r, c * ‖z - z'‖ ≤ ‖G z - G z'‖) ∧ ∀ z ∈ Metric.closedBall x r, ∀ v : Rn n, c * ‖v‖ ≤ ‖fderiv ℝ G z v‖`

## Sibling prerequisites

- None.

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
