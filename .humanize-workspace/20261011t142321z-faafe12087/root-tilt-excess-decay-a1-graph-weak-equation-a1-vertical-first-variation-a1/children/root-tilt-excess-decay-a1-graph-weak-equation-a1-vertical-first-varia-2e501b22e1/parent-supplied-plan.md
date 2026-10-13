# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.tilt_excess_decay-a1.graph_weak_equation-a1.vertical_first_variation-a1.height_localization-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/nodes/root-tilt-excess-decay-a1-graph-weak-equation-a1-vertical-first-varia-2e501b22e1/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.tilt_excess_decay-a1.graph_weak_equation-a1.vertical_first_variation-a1`
- Child key: `height_localization`
- Declaration: `Submission.gwe_vfv_norm_le_first_block_add_infDist`
- Exact Lean type: `∀ (n ℓ : ℕ) (q : Amb n ℓ ≃ₗᵢ[ℝ] Amb n ℓ) (x : Amb n ℓ), ‖x‖ ≤ ‖(EuclideanSpace.finAddEquivProd (q.symm x)).1‖ + infDist x (rotatedPlane q : Set (Amb n ℓ))`

## Sibling prerequisites

- `root.tilt_excess_height_estimate-a1.projection_algebra-a1`
- `root.lipschitz_approximation-a1.graph_coordinates-a1`

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
