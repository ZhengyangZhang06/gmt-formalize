# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.dimension_reduction_results-a1.moving_blowups-a1.deformation_theorem-a1.skeleton_deformation-a1.shell_decomposition-a1.boundary_mass_calculus-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-dimension-reduction-results-a1-moving-blowups-a1-deformation-the-090ddb3074/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.dimension_reduction_results-a1.moving_blowups-a1.deformation_theorem-a1.skeleton_deformation-a1.shell_decomposition-a1`
- Child key: `boundary_mass_calculus`
- Declaration: `Submission.dimred_mbl_dtsd_sh_boundaryMassOn_calculus`
- Exact Lean type: `∀ (P m : ℕ) (U G : Set (Euclid P)), (∀ X Y : GeometricCurrentOn U m, boundaryMassOn (X - Y) G ≤ boundaryMassOn X G + boundaryMassOn Y G) ∧ ∀ X : GeometricCurrentOn U (m + 1), boundaryMassOn X.boundary G = 0`

## Sibling prerequisites

- `root.compactness_of_minimizing_currents-a1.flat_convergence-a1.cauchy_subseq-a1.mass_sub_le-a1`

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
