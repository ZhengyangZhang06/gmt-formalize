# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.tangent_structure-a1.first_variation_pieces-a1.jacobian_derivative-a1.det_lower_bound-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T142930Z-d646011318/nodes/root-tangent-structure-a1-first-variation-pieces-a1-jacobian-derivati-ff844f2cab/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.tangent_structure-a1.first_variation_pieces-a1.jacobian_derivative-a1`
- Child key: `det_lower_bound`
- Declaration: `Submission.ts_fv_det_ge_pow_of_quadForm_ge`
- Exact Lean type: `∀ (N : ℕ) (S : Matrix (Fin N) (Fin N) ℝ) (c : ℝ), 0 ≤ c → (∀ i j, S i j = S j i) → (∀ ξ : Fin N → ℝ, c * ∑ i, ξ i ^ 2 ≤ ∑ i, ∑ j, ξ i * S i j * ξ j) → c ^ N ≤ S.det`

## Sibling prerequisites

- None.

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
