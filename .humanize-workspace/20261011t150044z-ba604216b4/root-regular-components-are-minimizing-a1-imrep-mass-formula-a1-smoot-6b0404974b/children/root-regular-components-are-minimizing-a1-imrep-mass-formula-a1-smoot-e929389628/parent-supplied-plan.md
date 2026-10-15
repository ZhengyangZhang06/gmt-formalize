# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.regular_components_are_minimizing-a1.imrep_mass_formula-a1.smooth_form_approx-a1.radial_retraction-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-regular-components-are-minimizing-a1-imrep-mass-formula-a1-smoot-e929389628/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.regular_components_are_minimizing-a1.imrep_mass_formula-a1.smooth_form_approx-a1`
- Child key: `radial_retraction`
- Declaration: `Submission.regcomp_norm_radial_retraction_sub_le`
- Exact Lean type: `∀ (E : Type) [NormedAddCommGroup E] [InnerProductSpace ℝ E] (x y : E), ‖y‖ ≤ 1 → ‖(max 1 ‖x‖)⁻¹ • x - y‖ ≤ ‖x - y‖`

## Sibling prerequisites

- None.

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
