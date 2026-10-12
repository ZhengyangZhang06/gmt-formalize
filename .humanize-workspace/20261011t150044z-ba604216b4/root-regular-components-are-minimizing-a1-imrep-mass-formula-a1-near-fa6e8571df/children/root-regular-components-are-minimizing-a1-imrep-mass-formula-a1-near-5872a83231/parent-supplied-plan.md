# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.regular_components_are_minimizing-a1.imrep_mass_formula-a1.near_maximizer-a1.unit_ball_dense_seq-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-regular-components-are-minimizing-a1-imrep-mass-formula-a1-near-5872a83231/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.regular_components_are_minimizing-a1.imrep_mass_formula-a1.near_maximizer-a1`
- Child key: `unit_ball_dense_seq`
- Declaration: `Submission.regcomp_covector_unit_ball_dense_seq`
- Exact Lean type: `∀ (P n : ℕ), ∃ b : ℕ → Covector (Euclid P) n, (∀ k, covectorEuclideanNorm (b k) ≤ 1) ∧ ∀ β : Covector (Euclid P) n, covectorEuclideanNorm β ≤ 1 → β ∈ closure (Set.range b)`

## Sibling prerequisites

- None.

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
