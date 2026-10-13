# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.compactness_of_minimizing_currents-a1.flat_convergence-a1.localize-a1.mass_add-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-compactness-of-minimizing-currents-a1-flat-convergence-a1-locali-dc88cf1feb/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.compactness_of_minimizing_currents-a1.flat_convergence-a1.localize-a1`
- Child key: `mass_add`
- Declaration: `Submission.cmc_fcl_massOn_le_add`
- Exact Lean type: `∀ (P d : ℕ) (U : Set (Euclid P)) (X Y Z : GeometricCurrentOn U d) (V : Set (Euclid P)), (∀ ω : TestFormOn U d, X ω = Y ω + Z ω) → X.massOn V ≤ Y.massOn V + Z.massOn V`

## Sibling prerequisites

- None.

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
