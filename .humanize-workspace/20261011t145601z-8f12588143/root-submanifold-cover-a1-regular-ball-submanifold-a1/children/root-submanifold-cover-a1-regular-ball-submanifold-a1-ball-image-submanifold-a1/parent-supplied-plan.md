# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.submanifold_cover-a1.regular_ball_submanifold-a1.ball_image_submanifold-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T145601Z-8f12588143/nodes/root-submanifold-cover-a1-regular-ball-submanifold-a1-ball-image-submanifold-a1/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.submanifold_cover-a1.regular_ball_submanifold-a1`
- Child key: `ball_image_submanifold`
- Declaration: `Submission.isC1Submanifold_image_ball_of_injOn_closedBall`
- Exact Lean type: `∀ (n p : ℕ) (G : Rn n → Rn p) (x : Rn n) (r : ℝ), ContDiffOn ℝ 1 G (Metric.closedBall x r) → Set.InjOn G (Metric.closedBall x r) → (∀ z ∈ Metric.ball x r, Function.Injective (fderiv ℝ G z)) → IsC1Submanifold n (G '' Metric.ball x r)`

## Sibling prerequisites

- None.

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
