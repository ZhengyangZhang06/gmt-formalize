# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.compactness_of_minimizing_currents-a1.zero_dim_minimizer_zero-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-compactness-of-minimizing-currents-a1-zero-dim-minimizer-zero-a1/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.compactness_of_minimizing_currents-a1`
- Child key: `zero_dim_minimizer_zero`
- Declaration: `Submission.cmc_zeroDim_minimizing_eq_zero`
- Exact Lean type: `∀ (P : ℕ) (U : Set (Euclid P)) (T : GeometricCurrentOn U 0), IsOpen U → IsMinimizingIn T U → T = 0`

## Sibling prerequisites

- `root.compactness_of_minimizing_currents-a1.mass_equals_rep_measure-a1`

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
