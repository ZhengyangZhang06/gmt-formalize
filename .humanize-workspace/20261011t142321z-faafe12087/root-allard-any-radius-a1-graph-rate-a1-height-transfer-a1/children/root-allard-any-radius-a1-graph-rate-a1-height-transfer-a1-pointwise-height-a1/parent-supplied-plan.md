# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.allard_any_radius-a1.graph_rate-a1.height_transfer-a1.pointwise_height-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/nodes/root-allard-any-radius-a1-graph-rate-a1-height-transfer-a1-pointwise-height-a1/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.allard_any_radius-a1.graph_rate-a1.height_transfer-a1`
- Child key: `pointwise_height`
- Declaration: `Submission.any_radius_gr_ht_pointwise_height`
- Exact Lean type: `∀ (n ℓ : ℕ) (q : Amb n ℓ ≃ₗᵢ[ℝ] Amb n ℓ) (P : Amb n ℓ →L[ℝ] Amb n ℓ) (A : Rn n →L[ℝ] Rn ℓ) (x : Rn n) (b : Rn ℓ), ‖A‖ ≤ 1 / 7 → ‖b‖ ≤ ‖x‖ / 7 → P (q (graphPoint x (A x))) = q (graphPoint x (A x)) → (∀ w : Rn ℓ, ‖w‖ ≤ Real.sqrt (1 + ‖A‖ ^ 2) * ‖q (graphPoint (0 : Rn n) w) - P (q (graphPoint (0 : Rn n) w))‖) → ‖b - A x‖ ^ 2 / ‖x‖ ^ (n + 2) ≤ 2 ^ (n + 4) * (‖q (graphPoint x b) - P (q (graphPoint x b))‖ ^ 2 / ‖q (graphPoint x b)‖ ^ (n + 2))`

## Sibling prerequisites

- None.

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
