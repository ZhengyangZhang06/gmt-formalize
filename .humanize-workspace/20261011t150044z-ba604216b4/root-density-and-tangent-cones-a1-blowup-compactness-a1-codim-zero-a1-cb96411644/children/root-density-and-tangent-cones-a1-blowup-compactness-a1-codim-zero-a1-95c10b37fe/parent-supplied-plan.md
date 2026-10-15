# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.density_and_tangent_cones-a1.blowup_compactness-a1.codim_zero-a1.blowup_eval-a1.dilation_ball-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-density-and-tangent-cones-a1-blowup-compactness-a1-codim-zero-a1-95c10b37fe/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.density_and_tangent_cones-a1.blowup_compactness-a1.codim_zero-a1.blowup_eval-a1`
- Child key: `dilation_ball`
- Declaration: `Submission.dtc_bc_cz_blowUp_eval_dilation_ball`
- Exact Lean type: `∀ (P : ℕ) (x : Euclid P) (ρ lam : ℝ), 0 < lam → dilation x lam ⁻¹' ball 0 (ρ / lam) = ball x ρ ∧ dilation x lam '' ball x ρ = ball 0 (ρ / lam)`

## Sibling prerequisites

- None.

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
