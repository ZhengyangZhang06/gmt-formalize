# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.tangent_structure-a1.first_variation_pieces-a1.jacobian_derivative-a1.tangential_estimates-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T142930Z-d646011318/nodes/root-tangent-structure-a1-first-variation-pieces-a1-jacobian-derivati-12a68937a7/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.tangent_structure-a1.first_variation_pieces-a1.jacobian_derivative-a1`
- Child key: `tangential_estimates`
- Declaration: `Submission.ts_fv_tangential_matrix_estimates`
- Exact Lean type: `∀ (N : ℕ) (P : Submodule ℝ (EuclideanSpace ℝ (Fin N))) (L : EuclideanSpace ℝ (Fin N) →L[ℝ] EuclideanSpace ℝ (Fin N)) (b : ℝ), 1 ≤ b → ‖L‖ ≤ b → (∀ v, ‖v‖ ≤ b * ‖L v‖) → (∀ i j : Fin N, |inner ℝ (L (P.starProjection (EuclideanSpace.single i (1 : ℝ)))) (L (P.starProjection (EuclideanSpace.single j (1 : ℝ)))) + inner ℝ (EuclideanSpace.single i (1 : ℝ) - P.starProjection (EuclideanSpace.single i (1 : ℝ))) (EuclideanSpace.single j (1 : ℝ) - P.starProjection (EuclideanSpace.single j (1 : ℝ)))| ≤ b ^ 2 + 1) ∧ ∀ ξ : Fin N → ℝ, (b ^ 2)⁻¹ * ∑ i, ξ i ^ 2 ≤ ∑ i, ∑ j, ξ i * (inner ℝ (L (P.starProjection (EuclideanSpace.single i (1 : ℝ)))) (L (P.starProjection (EuclideanSpace.single j (1 : ℝ)))) + inner ℝ (EuclideanSpace.single i (1 : ℝ) - P.starProjection (EuclideanSpace.single i (1 : ℝ))) (EuclideanSpace.single j (1 : ℝ) - P.starProjection (EuclideanSpace.single j (1 : ℝ)))) * ξ j`

## Sibling prerequisites

- None.

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
