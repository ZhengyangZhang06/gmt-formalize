# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.half_space_cone_lies_in_boundary-a1.imrep_support_eq_measure_support-a1.weight_null_where_current_vanishes-a1.covector_space_finite_dimensional-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-half-space-cone-lies-in-boundary-a1-imrep-support-eq-measure-sup-8f5d9ea2e2/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.half_space_cone_lies_in_boundary-a1.imrep_support_eq_measure_support-a1.weight_null_where_current_vanishes-a1`
- Child key: `covector_space_finite_dimensional`
- Declaration: `Submission.imsupp_covector_finiteDimensional`
- Exact Lean type: `∀ (P n : ℕ), FiniteDimensional ℝ (Covector (Euclid P) n)`

## Sibling prerequisites

- None.

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
