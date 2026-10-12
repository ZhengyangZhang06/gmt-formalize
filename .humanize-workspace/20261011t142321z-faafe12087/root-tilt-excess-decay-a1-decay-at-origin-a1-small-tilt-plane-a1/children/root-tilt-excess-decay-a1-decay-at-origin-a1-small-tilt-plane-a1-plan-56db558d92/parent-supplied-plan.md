# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.tilt_excess_decay-a1.decay_at_origin-a1.small_tilt_plane-a1.plane_dist_transfer-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/nodes/root-tilt-excess-decay-a1-decay-at-origin-a1-small-tilt-plane-a1-plan-56db558d92/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.tilt_excess_decay-a1.decay_at_origin-a1.small_tilt_plane-a1`
- Child key: `plane_dist_transfer`
- Declaration: `Submission.tdo_stp_infDist_le_infDist_add_hsNorm`
- Exact Lean type: `∀ (n ℓ : ℕ) (P Q : Submodule ℝ (Amb n ℓ)) (x : Amb n ℓ), infDist x (P : Set (Amb n ℓ)) ≤ infDist x (Q : Set (Amb n ℓ)) + hsNorm (P.starProjection - Q.starProjection) * ‖x‖`

## Sibling prerequisites

- `root.lipschitz_graph_corollary-a1.hole_estimate-a1.hs_norm_bounds-a1`

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
