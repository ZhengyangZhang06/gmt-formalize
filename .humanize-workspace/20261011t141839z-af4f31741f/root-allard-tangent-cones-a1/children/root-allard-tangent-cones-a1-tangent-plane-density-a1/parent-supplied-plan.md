# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.allard_tangent_cones-a1.tangent_plane_density-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T141839Z-af4f31741f/nodes/root-allard-tangent-cones-a1-tangent-plane-density-a1/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.allard_tangent_cones-a1`
- Child key: `tangent_plane_density`
- Declaration: `Submission.allard_tc_tangent_plane_density`
- Exact Lean type: `∀ (N n : ℕ) (U : Set (Euclidean N)) (V : Varifold N n U) (x : Euclidean N) (T : Grassmannian N n) (θ : ℝ), HasTangentPlane V x T θ → HasDensity n V.weight x (ENNReal.ofReal θ)`

## Sibling prerequisites

- `root.allard_tangent_cones-a1.flat_blowup_ball_limits-a1`

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
