# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.compactness_of_minimizing_currents-a1.closure_and_boundary_rectifiability-a1.cycle_im-a1.density_rep-a1.dual_norm-a1.norm_compare-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-compactness-of-minimizing-currents-a1-closure-and-boundary-recti-143968f697/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.compactness_of_minimizing_currents-a1.closure_and_boundary_rectifiability-a1.cycle_im-a1.density_rep-a1.dual_norm-a1`
- Child key: `norm_compare`
- Declaration: `Submission.cbr_ci_dr_dn_norm_le_mul_covectorEuclideanNorm`
- Exact Lean type: `∀ (P n : ℕ), ∃ K : ℝ, 0 < K ∧ ∀ α : Covector (Euclid P) n, ‖α‖ ≤ K * covectorEuclideanNorm α`

## Sibling prerequisites

- `root.compactness_of_minimizing_currents-a1.closure_and_boundary_rectifiability-a1.cycle_im-a1.density_rep-a1.dual_norm-a1.coord_definite-a1`
- `root.density_one_implies_regular-a1.imrep_mass_and_support-a1.lusin_covector-a1.covector_finite_dimensional-a1`

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
