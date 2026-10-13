# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.tilt_excess_decay-a1.decay_at_origin-a1.graph_plane_dist-a1.graph_plane_finrank-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/nodes/root-tilt-excess-decay-a1-decay-at-origin-a1-graph-plane-dist-a1-grap-f97a789982/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.tilt_excess_decay-a1.decay_at_origin-a1.graph_plane_dist-a1`
- Child key: `graph_plane_finrank`
- Declaration: `Submission.tdo_gpd_graph_plane_finrank`
- Exact Lean type: `∀ (n ℓ : ℕ) (q : Amb n ℓ ≃ₗᵢ[ℝ] Amb n ℓ) (A : Rn n →L[ℝ] Rn ℓ), Module.finrank ℝ (Submodule.span ℝ (Set.range fun v : Rn n => q (graphPoint v (A v)))) = n`

## Sibling prerequisites

- `root.regular_set_open_dense-a1.c1_submanifold_graph_ball-a1.graph_point_linear_equiv-a1`

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
