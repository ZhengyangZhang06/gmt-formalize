# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.first_rectifiability-a1.tangent_density-a1.plane_ball-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T141839Z-af4f31741f/nodes/root-first-rectifiability-a1-tangent-density-a1-plane-ball-a1/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.first_rectifiability-a1.tangent_density-a1`
- Child key: `plane_ball`
- Declaration: `Submission.frt_td_plane_closedBall_hausdorff`
- Exact Lean type: `∀ (N n : ℕ) (T : Grassmannian N n) (r : ℝ), 0 ≤ r → (μHE[n] : Measure (Euclidean N)) ((T.plane : Set (Euclidean N)) ∩ closedBall 0 r) = unitBallVolume n * ENNReal.ofReal r ^ n`

## Sibling prerequisites

- None.

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
