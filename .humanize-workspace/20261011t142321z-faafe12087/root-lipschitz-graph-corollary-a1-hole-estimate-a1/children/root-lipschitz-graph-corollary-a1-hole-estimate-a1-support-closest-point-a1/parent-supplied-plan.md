# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.lipschitz_graph_corollary-a1.hole_estimate-a1.support_closest_point-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/nodes/root-lipschitz-graph-corollary-a1-hole-estimate-a1-support-closest-point-a1/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.lipschitz_graph_corollary-a1.hole_estimate-a1`
- Child key: `support_closest_point`
- Declaration: `Submission.lgc_support_closest_point`
- Exact Lean type: `∀ (n ℓ : ℕ) (U : Set (Amb n ℓ)) (V : RectifiableVarifold n ℓ U) (ρ : ℝ) (ζ : Amb n ℓ), (0 : Amb n ℓ) ∈ V.support → closedBall (0 : Amb n ℓ) ρ ⊆ U → ‖ζ‖ + infDist ζ V.support ≤ ρ → ∃ y ∈ V.support, dist y ζ = infDist ζ V.support ∧ V.weight (ball ζ (infDist ζ V.support)) = 0`

## Sibling prerequisites

- None.

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
