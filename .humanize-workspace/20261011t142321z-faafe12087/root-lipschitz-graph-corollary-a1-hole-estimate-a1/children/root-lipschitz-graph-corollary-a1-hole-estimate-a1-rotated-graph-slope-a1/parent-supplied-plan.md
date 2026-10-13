# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.lipschitz_graph_corollary-a1.hole_estimate-a1.rotated_graph_slope-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/nodes/root-lipschitz-graph-corollary-a1-hole-estimate-a1-rotated-graph-slope-a1/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.lipschitz_graph_corollary-a1.hole_estimate-a1`
- Child key: `rotated_graph_slope`
- Declaration: `Submission.lgc_rotated_graph_slope`
- Exact Lean type: `∀ (n ℓ : ℕ) (q : Amb n ℓ ≃ₗᵢ[ℝ] Amb n ℓ) (f : Rn n → Rn ℓ) (ε : ℝ), 0 ≤ ε → LipschitzWith (Real.toNNReal ε) f → IsClosed (q '' graphOver f univ) ∧ ∀ x ∈ q '' graphOver f univ, ∀ z ∈ q '' graphOver f univ, ‖(x - z) - (rotatedPlane q).starProjection (x - z)‖ ≤ ε * ‖x - z‖`

## Sibling prerequisites

- None.

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
