# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.integral_compactness-a1.integral_density-a1.tangent_point_density-a1.plane_ball-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T141839Z-af4f31741f/nodes/root-integral-compactness-a1-integral-density-a1-tangent-point-densit-8355c73f93/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.integral_compactness-a1.integral_density-a1.tangent_point_density-a1`
- Child key: `plane_ball`
- Declaration: `Submission.intcpt_id_tpd_plane_closedBall_hausdorff`
- Exact Lean type: `∀ (N n : ℕ) (P : Submodule ℝ (Euclidean N)) (r : ℝ), Module.finrank ℝ P = n → 0 ≤ r → (μHE[n] : Measure (Euclidean N)) ((P : Set (Euclidean N)) ∩ closedBall 0 r) = unitBallVolume n * ENNReal.ofReal r ^ n`

## Sibling prerequisites

- None.

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
