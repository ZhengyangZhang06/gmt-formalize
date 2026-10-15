# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.compactness_of_minimizing_currents-a1.closure_and_boundary_rectifiability-a1.cycle_im-a1.density_rep-a1.dual_norm-a1.coord_definite-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-compactness-of-minimizing-currents-a1-closure-and-boundary-recti-d6049bd71f/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.compactness_of_minimizing_currents-a1.closure_and_boundary_rectifiability-a1.cycle_im-a1.density_rep-a1.dual_norm-a1`
- Child key: `coord_definite`
- Declaration: `Submission.cbr_ci_dr_dn_covector_eq_zero_of_coords`
- Exact Lean type: `∀ (P n : ℕ) (α : Covector (Euclid P) n), (∀ I : Fin n → Fin P, StrictMono I → α (fun i => EuclideanSpace.basisFun (Fin P) ℝ (I i)) = 0) → α = 0`

## Sibling prerequisites

- None.

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
