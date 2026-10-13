# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.density_one_higher_regularity-a1.elliptic_bootstrap-a1.area_integrand_legendre-a1.line_second_deriv-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/nodes/root-density-one-higher-regularity-a1-elliptic-bootstrap-a1-area-inte-5f815e0d10/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.density_one_higher_regularity-a1.elliptic_bootstrap-a1.area_integrand_legendre-a1`
- Child key: `line_second_deriv`
- Declaration: `Submission.dohr_eb_ail_line_second_deriv`
- Exact Lean type: `∀ {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] (F : E → ℝ), ContDiff ℝ 2 F → ∀ x v : E, deriv (deriv (fun t : ℝ => F (x + t • v))) 0 = fderiv ℝ (fderiv ℝ F) x v v`

## Sibling prerequisites

- None.

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
