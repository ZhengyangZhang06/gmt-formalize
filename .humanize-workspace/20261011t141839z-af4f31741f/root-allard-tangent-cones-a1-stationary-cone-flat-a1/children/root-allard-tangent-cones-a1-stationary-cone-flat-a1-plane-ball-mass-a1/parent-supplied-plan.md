# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.allard_tangent_cones-a1.stationary_cone_flat-a1.plane_ball_mass-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T141839Z-af4f31741f/nodes/root-allard-tangent-cones-a1-stationary-cone-flat-a1-plane-ball-mass-a1/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.allard_tangent_cones-a1.stationary_cone_flat-a1`
- Child key: `plane_ball_mass`
- Declaration: `Submission.allard_tc_scf_plane_ball_mass`
- Exact Lean type: `∀ (N n : ℕ) (T : Grassmannian N n) (r : ℝ), 0 < r → planeVarifoldMeasure T (closedBall (0 : Euclidean N) r ×ˢ (univ : Set (Grassmannian N n))) = unitBallVolume n * ENNReal.ofReal r ^ n`

## Sibling prerequisites

- None.

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
