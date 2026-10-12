# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.lipschitz_approximation-a1.graph_measure-a1.ball_measure-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/nodes/root-lipschitz-approximation-a1-graph-measure-a1-ball-measure-a1/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.lipschitz_approximation-a1.graph_measure-a1`
- Child key: `ball_measure`
- Declaration: `Submission.lip_approx_gm_ball_measure`
- Exact Lean type: `∀ (n : ℕ), 1 ≤ n → ∀ (c : Rn n) (r : ℝ), 0 ≤ r → (μHE[n] : Measure (Rn n)) (closedBall c r) = ENNReal.ofReal (unitBallVolume n * r ^ n)`

## Sibling prerequisites

- None.

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
