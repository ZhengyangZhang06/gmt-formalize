# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.density_and_tangent_cones-a1.blowup_compactness-a1.codim_zero-a1.minimizing-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-density-and-tangent-cones-a1-blowup-compactness-a1-codim-zero-a1-26ab64b330/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.density_and_tangent_cones-a1.blowup_compactness-a1.codim_zero-a1`
- Child key: `minimizing`
- Declaration: `Submission.dtc_bc_cz_isMinimizingIn`
- Exact Lean type: `∀ (n : ℕ) (C : GeometricCurrentOn (univ : Set (Euclid n)) n) (A : Set (Euclid n)), 0 < n → IsIntegerMultiplicity C → IsMinimizingIn C A`

## Sibling prerequisites

- `root.density_and_tangent_cones-a1.blowup_compactness-a1.codim_zero-a1.top_constancy-a1`
- `root.density_and_tangent_cones-a1.im_sub-a1`
- `root.density_and_tangent_cones-a1.vanish_off_support-a1`

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
