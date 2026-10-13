# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.compactness_of_minimizing_currents-a1.slicing-a1.wedge_norm-a1.fiber_sum-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-compactness-of-minimizing-currents-a1-slicing-a1-wedge-norm-a1-fiber-sum-a1/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.compactness_of_minimizing_currents-a1.slicing-a1.wedge_norm-a1`
- Child key: `fiber_sum`
- Declaration: `Submission.cmcs_wn_removeNth_fiber_sum`
- Exact Lean type: `∀ (k P : ℕ) (i₀ : Fin P) (F : (Fin k → Fin P) → ℝ), ∑ j : Fin (k + 1) → Fin P, ∑ i : Fin (k + 1), (if j i = i₀ then F (i.removeNth j) else 0) = ((k : ℝ) + 1) * ∑ j' : Fin k → Fin P, F j'`

## Sibling prerequisites

- None.

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
