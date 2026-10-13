# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.allard_any_radius-a1.graph_rate-a1.la_basics-a1.rotated_plane-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/nodes/root-allard-any-radius-a1-graph-rate-a1-la-basics-a1-rotated-plane-a1/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.allard_any_radius-a1.graph_rate-a1.la_basics-a1`
- Child key: `rotated_plane`
- Declaration: `Submission.any_radius_gr_la_rotatedPlane_facts`
- Exact Lean type: `∀ (n ℓ : ℕ) (q : Amb n ℓ ≃ₗᵢ[ℝ] Amb n ℓ), (∀ (a : Rn n) (b : Rn ℓ), (rotatedPlane q).starProjection (q (graphPoint a b)) = q (graphPoint a (0 : Rn ℓ))) ∧ (∀ (a : Rn n) (b : Rn ℓ), infDist (q (graphPoint a b)) (rotatedPlane q : Set (Amb n ℓ)) = ‖b‖) ∧ Module.finrank ℝ (rotatedPlane q) = n`

## Sibling prerequisites

- `root.allard_any_radius-a1.graph_rate-a1.la_basics-a1.graph_coords-a1`

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
