# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.allard_regularity-a1.graph_campanato-a1.campanato_from_tilt-a1.graph_sqrt_two-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/nodes/root-allard-regularity-a1-graph-campanato-a1-campanato-from-tilt-a1-g-ee44f55667/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.allard_regularity-a1.graph_campanato-a1.campanato_from_tilt-a1`
- Child key: `graph_sqrt_two`
- Declaration: `Submission.allard52_cft_graph_map_sqrt_two`
- Exact Lean type: `∀ (n ℓ : ℕ) (q : Amb n ℓ ≃ₗᵢ[ℝ] Amb n ℓ) (f : Rn n → Rn ℓ) (D : Set (Rn n)), LipschitzOnWith 1 f D → (∀ x ∈ D, ∀ x' ∈ D, ‖q (graphPoint x (f x)) - q (graphPoint x' (f x'))‖ ≤ Real.sqrt 2 * ‖x - x'‖) ∧ (f 0 = 0 → (0 : Rn n) ∈ D → ∀ x ∈ D, ‖q (graphPoint x (f x))‖ ≤ Real.sqrt 2 * ‖x‖)`

## Sibling prerequisites

- `root.lipschitz_approximation-a1.graph_coordinates-a1`

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
