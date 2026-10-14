# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.compactness_of_minimizing_currents-a1.deformation_theorem-a1.cube_bv_median-a1.bv_poincare-a1.mean_dev-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-compactness-of-minimizing-currents-a1-deformation-theorem-a1-cub-74a87ebba5/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.compactness_of_minimizing_currents-a1.deformation_theorem-a1.cube_bv_median-a1.bv_poincare-a1`
- Child key: `mean_dev`
- Declaration: `Submission.cmcdt_cbm_bvp_mean_dev_le_osc`
- Exact Lean type: `∀ (m : ℕ) (S : Set (Euclid (m + 1))) (u : Euclid (m + 1) → ℝ), volume S = 1 → IntegrableOn u S → ∫ x in S, |u x - ∫ y in S, u y| ≤ ∫ x in S, ∫ y in S, |u x - u y|`

## Sibling prerequisites

- None.

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
