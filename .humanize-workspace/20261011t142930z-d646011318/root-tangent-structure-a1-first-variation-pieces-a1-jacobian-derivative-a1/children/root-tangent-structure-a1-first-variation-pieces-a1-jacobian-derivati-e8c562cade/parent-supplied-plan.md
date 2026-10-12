# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.tangent_structure-a1.first_variation_pieces-a1.jacobian_derivative-a1.jacobi_formula-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T142930Z-d646011318/nodes/root-tangent-structure-a1-first-variation-pieces-a1-jacobian-derivati-e8c562cade/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.tangent_structure-a1.first_variation_pieces-a1.jacobian_derivative-a1`
- Child key: `jacobi_formula`
- Declaration: `Submission.ts_fv_hasDerivAt_det_of_entries`
- Exact Lean type: `∀ (N : ℕ) (A : ℝ → Matrix (Fin N) (Fin N) ℝ) (A' : Matrix (Fin N) (Fin N) ℝ) (t M M' : ℝ), (∀ i j, HasDerivAt (fun s ↦ A s i j) (A' i j) t) → (∀ i j, |A t i j| ≤ M) → (∀ i j, |A' i j| ≤ M') → ∃ D : ℝ, HasDerivAt (fun s ↦ (A s).det) D t ∧ |D| ≤ (N.factorial : ℝ) * N * M' * M ^ (N - 1) ∧ (A t = 1 → D = A'.trace)`

## Sibling prerequisites

- None.

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
