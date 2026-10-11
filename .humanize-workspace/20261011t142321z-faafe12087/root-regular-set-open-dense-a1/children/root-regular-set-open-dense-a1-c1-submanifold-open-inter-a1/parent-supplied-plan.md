# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.regular_set_open_dense-a1.c1_submanifold_open_inter-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/nodes/root-regular-set-open-dense-a1-c1-submanifold-open-inter-a1/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.regular_set_open_dense-a1`
- Child key: `c1_submanifold_open_inter`
- Declaration: `Submission.rsod_isC1Submanifold_open_inter`
- Exact Lean type: `∀ (m N : ℕ) (S B : Set (EuclideanSpace ℝ (Fin N))), IsC1Submanifold m S → IsOpen B → IsC1Submanifold m (B ∩ S)`

## Sibling prerequisites

- None.

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
