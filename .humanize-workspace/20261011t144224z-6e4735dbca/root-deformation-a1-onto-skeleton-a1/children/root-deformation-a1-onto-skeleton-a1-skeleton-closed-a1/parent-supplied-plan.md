# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.deformation-a1.onto_skeleton-a1.skeleton_closed-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/nodes/root-deformation-a1-onto-skeleton-a1-skeleton-closed-a1/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.deformation-a1.onto_skeleton-a1`
- Child key: `skeleton_closed`
- Declaration: `Submission.deformation_skeleton_isClosed`
- Exact Lean type: `∀ (n N : ℕ) (ρ : ℝ), 0 < ρ → IsClosed (⋃ F : LatticeFaceIndex n N, latticeFace ρ F)`

## Sibling prerequisites

- None.

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
