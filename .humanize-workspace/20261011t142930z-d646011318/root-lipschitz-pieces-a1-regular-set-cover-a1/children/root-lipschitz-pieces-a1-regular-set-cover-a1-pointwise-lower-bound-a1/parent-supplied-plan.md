# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.lipschitz_pieces-a1.regular_set_cover-a1.pointwise_lower_bound-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T142930Z-d646011318/nodes/root-lipschitz-pieces-a1-regular-set-cover-a1-pointwise-lower-bound-a1/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.lipschitz_pieces-a1.regular_set_cover-a1`
- Child key: `pointwise_lower_bound`
- Declaration: `Submission.injective_fderiv_local_lower_bound`
- Exact Lean type: `∀ (n : ℕ) {F : Type} [NormedAddCommGroup F] [NormedSpace ℝ F] (f : EuclideanSpace ℝ (Fin n) → F) (w : EuclideanSpace ℝ (Fin n)), DifferentiableAt ℝ f w → Function.Injective (fderiv ℝ f w) → ∃ c : ℝ, 0 < c ∧ ∀ u : EuclideanSpace ℝ (Fin n), ‖u‖ ≤ c → c * ‖u‖ ≤ ‖f (w + u) - f w‖`

## Sibling prerequisites

- None.

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
