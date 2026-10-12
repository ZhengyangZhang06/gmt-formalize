# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.tangent_structure-a1.piece_tangent_field-a1.piece_projection_continuity-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T142930Z-d646011318/nodes/root-tangent-structure-a1-piece-tangent-field-a1-piece-projection-continuity-a1/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.tangent_structure-a1.piece_tangent_field-a1`
- Child key: `piece_projection_continuity`
- Declaration: `Submission.ts_piece_projection_continuousOn_image`
- Exact Lean type: `∀ (n ℓ : ℕ) (C : Set (EuclideanSpace ℝ (Fin n))) (F : EuclideanSpace ℝ (Fin n) → Ambient n ℓ) (c : ℝ), 0 < c → (∀ v ∈ C, ∀ w ∈ C, c * ‖v - w‖ ≤ ‖F v - F w‖) → (∀ w ∈ C, Function.Injective (fderiv ℝ F w)) → ContinuousOn (fderiv ℝ F) C → ∃ G : Ambient n ℓ → (Ambient n ℓ →L[ℝ] Ambient n ℓ), ContinuousOn G (F '' C) ∧ ∀ w ∈ C, G (F w) = (LinearMap.range (fderiv ℝ F w).toLinearMap).starProjection`

## Sibling prerequisites

- `root.tangent_structure-a1.piece_tangent_field-a1.projection_continuity-a1`

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
