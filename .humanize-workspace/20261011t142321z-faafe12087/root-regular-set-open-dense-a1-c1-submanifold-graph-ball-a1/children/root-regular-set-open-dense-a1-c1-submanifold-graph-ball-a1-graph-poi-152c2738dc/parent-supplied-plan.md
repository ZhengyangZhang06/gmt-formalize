# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.regular_set_open_dense-a1.c1_submanifold_graph_ball-a1.graph_point_linear_equiv-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/nodes/root-regular-set-open-dense-a1-c1-submanifold-graph-ball-a1-graph-poi-152c2738dc/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.regular_set_open_dense-a1.c1_submanifold_graph_ball-a1`
- Child key: `graph_point_linear_equiv`
- Declaration: `Submission.rsod_graphPoint_eq_finAddEquivProd_symm`
- Exact Lean type: `∀ {n ℓ : ℕ} (x : Rn n) (y : Rn ℓ), graphPoint x y = (EuclideanSpace.finAddEquivProd : Amb n ℓ ≃L[ℝ] Rn n × Rn ℓ).symm (x, y)`

## Sibling prerequisites

- None.

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
