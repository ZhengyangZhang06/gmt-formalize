# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.regular_set_open_dense-a1.c1_submanifold_graph_ball-a1.norm_graph_point_sq-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/nodes/root-regular-set-open-dense-a1-c1-submanifold-graph-ball-a1-norm-grap-4075ba9057/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.regular_set_open_dense-a1.c1_submanifold_graph_ball-a1`
- Child key: `norm_graph_point_sq`
- Declaration: `Submission.rsod_norm_graphPoint_sq`
- Exact Lean type: `∀ {n ℓ : ℕ} (x : Rn n) (y : Rn ℓ), ‖graphPoint x y‖ ^ 2 = ‖x‖ ^ 2 + ‖y‖ ^ 2`

## Sibling prerequisites

- None.

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
