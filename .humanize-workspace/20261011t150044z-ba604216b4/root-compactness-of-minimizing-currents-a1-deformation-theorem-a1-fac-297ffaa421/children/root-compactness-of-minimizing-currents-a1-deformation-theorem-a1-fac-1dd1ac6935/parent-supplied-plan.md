# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.compactness_of_minimizing_currents-a1.deformation_theorem-a1.face_replacement-a1.skeleton_null-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-compactness-of-minimizing-currents-a1-deformation-theorem-a1-fac-1dd1ac6935/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.compactness_of_minimizing_currents-a1.deformation_theorem-a1.face_replacement-a1`
- Child key: `skeleton_null`
- Declaration: `Submission.cmcdtfr_skeleton_null`
- Exact Lean type: `∀ (P m : ℕ), μHE[m + 1] {x : Euclid P | ∃ s : Finset (Fin P), P ≤ m + s.card ∧ ∀ i ∈ s, ∃ z : ℤ, x i = z} = 0`

## Sibling prerequisites

- None.

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
