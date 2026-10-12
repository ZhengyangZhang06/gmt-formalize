# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.rectifiability-a1.projection_null-a1.potential_estimate-a1.polar_integral-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/nodes/root-rectifiability-a1-projection-null-a1-potential-estimate-a1-polar-a527f3fd17/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.rectifiability-a1.projection_null-a1.potential_estimate-a1`
- Child key: `polar_integral`
- Declaration: `Submission.rpn_pe_integral_eq_polar`
- Exact Lean type: `∀ (m : ℕ) (g : Eucl (m + 1) → ℝ), Integrable g → ∫ x, g x = ∫ θ : sphere (0 : Eucl (m + 1)) 1, (∫ r in Ioi (0 : ℝ), r ^ m * g (r • (θ : Eucl (m + 1)))) ∂(volume : Measure (Eucl (m + 1))).toSphere`

## Sibling prerequisites

- None.

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
