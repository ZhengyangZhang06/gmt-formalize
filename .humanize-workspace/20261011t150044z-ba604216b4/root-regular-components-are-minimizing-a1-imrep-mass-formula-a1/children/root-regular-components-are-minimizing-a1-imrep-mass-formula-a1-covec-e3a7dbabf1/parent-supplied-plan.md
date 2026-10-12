# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.regular_components_are_minimizing-a1.imrep_mass_formula-a1.covector_norming-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-regular-components-are-minimizing-a1-imrep-mass-formula-a1-covec-e3a7dbabf1/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.regular_components_are_minimizing-a1.imrep_mass_formula-a1`
- Child key: `covector_norming`
- Declaration: `Submission.regcomp_exists_covector_eval_orthonormal_eq_one`
- Exact Lean type: `∀ (P n : ℕ) (τ : Fin n → Euclid P), Orthonormal ℝ τ → ∃ β : Covector (Euclid P) n, covectorEuclideanNorm β = 1 ∧ β τ = 1`

## Sibling prerequisites

- `root.regular_components_are_minimizing-a1.imrep_mass_formula-a1.covector_sq_sum-a1`

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
