# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.regular_components_are_minimizing-a1.imrep_mass_formula-a1.smooth_form_approx-a1.opnorm_basis_bound-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-regular-components-are-minimizing-a1-imrep-mass-formula-a1-smoot-edbd9a939c/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.regular_components_are_minimizing-a1.imrep_mass_formula-a1.smooth_form_approx-a1`
- Child key: `opnorm_basis_bound`
- Declaration: `Submission.regcomp_covector_opNorm_le_of_basis_bound`
- Exact Lean type: `∀ (P n : ℕ) (α : Covector (Euclid P) n) (C : ℝ), 0 ≤ C → (∀ j : Fin n → Fin P, |α (fun k => EuclideanSpace.basisFun (Fin P) ℝ (j k))| ≤ C) → ‖α‖ ≤ (P : ℝ) ^ n * C`

## Sibling prerequisites

- None.

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
