# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.rectifiability-a1.projection_null-a1.potential_estimate-a1.kernel_local_integrable-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/nodes/root-rectifiability-a1-projection-null-a1-potential-estimate-a1-kerne-c743f8cc19/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.rectifiability-a1.projection_null-a1.potential_estimate-a1`
- Child key: `kernel_local_integrable`
- Declaration: `Submission.rpn_pe_kernel_locallyIntegrable`
- Exact Lean type: `∀ (m : ℕ) (j : Fin (m + 1)) (c : ℝ), LocallyIntegrable (fun t : Eucl (m + 1) => t j / (c * ‖t‖ ^ (m + 1)))`

## Sibling prerequisites

- `root.rectifiability-a1.projection_null-a1.potential_estimate-a1.radial_ball_integral-a1`

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
