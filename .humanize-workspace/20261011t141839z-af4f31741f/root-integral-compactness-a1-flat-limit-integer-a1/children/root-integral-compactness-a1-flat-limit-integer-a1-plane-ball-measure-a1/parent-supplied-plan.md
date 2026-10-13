# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.integral_compactness-a1.flat_limit_integer-a1.plane_ball_measure-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T141839Z-af4f31741f/nodes/root-integral-compactness-a1-flat-limit-integer-a1-plane-ball-measure-a1/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.integral_compactness-a1.flat_limit_integer-a1`
- Child key: `plane_ball_measure`
- Declaration: `Submission.intcpt_fli_plane_ball_measure`
- Exact Lean type: `∀ (N n : ℕ) (T : Grassmannian N n) (a : Euclidean N) (r : ℝ), a ∈ T.plane → 0 < r → (μHE[n] : Measure (Euclidean N)) ((T.plane : Set (Euclidean N)) ∩ closedBall a r) = unitBallVolume n * ENNReal.ofReal r ^ n ∧ (μHE[n] : Measure (Euclidean N)) ((T.plane : Set (Euclidean N)) ∩ ball a r) = unitBallVolume n * ENNReal.ofReal r ^ n`

## Sibling prerequisites

- None.

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
