# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.tilt_excess_decay-a1.decay_at_origin-a1.graph_plane_dist-a1.rotated_plane_dist-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/nodes/root-tilt-excess-decay-a1-decay-at-origin-a1-graph-plane-dist-a1-rota-341ecee7fe/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.tilt_excess_decay-a1.decay_at_origin-a1.graph_plane_dist-a1`
- Child key: `rotated_plane_dist`
- Declaration: `Submission.tdo_gpd_infDist_rotatedPlane_graphPoint`
- Exact Lean type: `∀ (n ℓ : ℕ) (q : Amb n ℓ ≃ₗᵢ[ℝ] Amb n ℓ) (a : Rn n) (b : Rn ℓ), infDist (q (graphPoint a b)) (rotatedPlane q : Set (Amb n ℓ)) = ‖b‖`

## Sibling prerequisites

- `root.lipschitz_approximation-a1.graph_coordinates-a1`

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
