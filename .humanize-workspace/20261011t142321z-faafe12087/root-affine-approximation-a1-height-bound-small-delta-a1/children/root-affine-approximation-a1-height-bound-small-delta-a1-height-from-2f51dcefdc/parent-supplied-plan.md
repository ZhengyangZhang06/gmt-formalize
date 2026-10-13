# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.affine_approximation-a1.height_bound_small_delta-a1.height_from_net_plane-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/nodes/root-affine-approximation-a1-height-bound-small-delta-a1-height-from-2f51dcefdc/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.affine_approximation-a1.height_bound_small_delta-a1`
- Child key: `height_from_net_plane`
- Declaration: `Submission.aal_height_of_net_plane`
- Exact Lean type: `∀ (n ℓ : ℕ) (T : Submodule ℝ (Amb n ℓ)) (ξ x₀ : Amb n ℓ) (S : Set (Amb n ℓ)) (F : Finset (Amb n ℓ)) (a b : ℝ), ‖x₀ - ξ‖ ≤ a → (∀ y ∈ F, ‖(x₀ - y) - T.starProjection (x₀ - y)‖ ≤ b) → (∀ x ∈ S, ∃ y ∈ F, dist x y ≤ a) → ∀ x ∈ S, infDist (x - ξ) (T : Set (Amb n ℓ)) ≤ b + 2 * a`

## Sibling prerequisites

- None.

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
