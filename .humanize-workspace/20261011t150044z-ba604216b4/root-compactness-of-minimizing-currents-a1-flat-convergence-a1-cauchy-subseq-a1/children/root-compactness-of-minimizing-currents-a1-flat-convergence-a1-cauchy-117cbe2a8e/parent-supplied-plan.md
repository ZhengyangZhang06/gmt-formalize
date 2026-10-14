# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.compactness_of_minimizing_currents-a1.flat_convergence-a1.cauchy_subseq-a1.mass_sub_le-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-compactness-of-minimizing-currents-a1-flat-convergence-a1-cauchy-117cbe2a8e/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.compactness_of_minimizing_currents-a1.flat_convergence-a1.cauchy_subseq-a1`
- Child key: `mass_sub_le`
- Declaration: `Submission.cmc_fc_cs_massOn_sub_le`
- Exact Lean type: `∀ (P n : ℕ) (U G : Set (Euclid P)) (A B : GeometricCurrentOn U n), (A - B).massOn G ≤ A.massOn G + B.massOn G`

## Sibling prerequisites

- None.

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
