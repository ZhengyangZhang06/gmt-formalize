# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.tangent_graph_cover-a1.cone_decay-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T141839Z-af4f31741f/nodes/root-tangent-graph-cover-a1-cone-decay-a1/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.tangent_graph_cover-a1`
- Child key: `cone_decay`
- Declaration: `Submission.tgc_tangent_cone_weight_decay`
- Exact Lean type: `∀ (N n : ℕ) (U : Set (Euclidean N)) (V : Varifold N n U) (x : Euclidean N) (T : Grassmannian N n) (θ : ℝ), 0 < n → HasTangentPlane V x T θ → ∀ β : ℝ, 0 < β → ∀ ε : ℝ≥0∞, 0 < ε → ∀ᶠ t in 𝓝[>] (0 : ℝ), V.weight {y | y ∈ closedBall x t ∧ β * ‖y - x‖ ≤ ‖(y - x) - Grassmannian.project T (y - x)‖} ≤ ε * ENNReal.ofReal t ^ n`

## Sibling prerequisites

- `root.tangent_graph_cover-a1.weight_blowup-a1`
- `root.tangent_graph_cover-a1.plane_ball_measure-a1`

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
