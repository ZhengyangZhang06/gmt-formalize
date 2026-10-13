# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.tilt_excess_decay-a1.graph_weak_equation-a1.graph_tilt_algebra-a1.vertical_trace_sum-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/nodes/root-tilt-excess-decay-a1-graph-weak-equation-a1-graph-tilt-algebra-a-62853e6db2/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.tilt_excess_decay-a1.graph_weak_equation-a1.graph_tilt_algebra-a1`
- Child key: `vertical_trace_sum`
- Declaration: `Submission.gwe_gta_vertical_trace_sum`
- Exact Lean type: `∀ (n ℓ : ℕ) (q : Amb n ℓ ≃ₗᵢ[ℝ] Amb n ℓ) (S : Submodule ℝ (Amb n ℓ)), Module.finrank ℝ S = n → ∑ j : Fin ℓ, ‖S.starProjection (q (graphPoint 0 (EuclideanSpace.single j (1 : ℝ))))‖ ^ 2 = hsNormSq (S.starProjection - (rotatedPlane q).starProjection) / 2`

## Sibling prerequisites

- `root.tilt_excess_height_estimate-a1.projection_algebra-a1`
- `root.allard_any_radius-a1.graph_rate-a1.la_basics-a1.graph_coords-a1`
- `root.allard_any_radius-a1.graph_rate-a1.la_basics-a1.rotated_plane-a1`

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
