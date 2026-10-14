# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.minimizing_implies_stationary-a1.support_null-a1.local_carrier_null-a1.covector_finite_dimensional-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-minimizing-implies-stationary-a1-support-null-a1-local-carrier-n-264afcab31/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.minimizing_implies_stationary-a1.support_null-a1.local_carrier_null-a1`
- Child key: `covector_finite_dimensional`
- Declaration: `Submission.lcn_covector_finiteDimensional`
- Exact Lean type: `∀ (P n : ℕ), FiniteDimensional ℝ (Covector (Euclid P) n)`

## Sibling prerequisites

- None.

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
