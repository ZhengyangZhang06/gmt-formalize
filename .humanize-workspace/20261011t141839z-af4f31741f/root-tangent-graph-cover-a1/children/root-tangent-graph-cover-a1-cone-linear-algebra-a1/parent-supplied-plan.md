# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.tangent_graph_cover-a1.cone_linear_algebra-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T141839Z-af4f31741f/nodes/root-tangent-graph-cover-a1-cone-linear-algebra-a1/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.tangent_graph_cover-a1`
- Child key: `cone_linear_algebra`
- Declaration: `Submission.tgc_tilted_cone_inclusion`
- Exact Lean type: `∀ (N n : ℕ) (L : ℝ) (P T : Grassmannian N n) (v w : Euclidean N), 0 < L → L ≤ 1 → (∀ u : Euclidean N, ‖Grassmannian.project T u - Grassmannian.project P u‖ ≤ L / 4 * ‖u‖) → L * ‖Grassmannian.project P v‖ < ‖v - Grassmannian.project P v‖ → ‖w - v‖ ≤ L / 8 * ‖v‖ → L / 16 * ‖w‖ ≤ ‖w - Grassmannian.project T w‖ ∧ ‖w‖ ≤ 2 * ‖v‖`

## Sibling prerequisites

- None.

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
