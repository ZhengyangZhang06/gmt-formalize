# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.compactness_of_minimizing_currents-a1.slicing-a1.wedge_norm-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-compactness-of-minimizing-currents-a1-slicing-a1-wedge-norm-a1/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.compactness_of_minimizing_currents-a1.slicing-a1`
- Child key: `wedge_norm`
- Declaration: `Submission.cmcs_wedge_norm_le`
- Exact Lean type: `∀ (P k : ℕ) (β : Euclid P →L[ℝ] ℝ) (γ : Covector (Euclid P) k), covectorEuclideanNorm (ContinuousAlternatingMap.alternatizeUncurryFin (β.smulRight γ)) ≤ ‖β‖ * covectorEuclideanNorm γ`

## Sibling prerequisites

- `root.regular_components_are_minimizing-a1.imrep_mass_formula-a1.covector_sq_sum-a1`

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
