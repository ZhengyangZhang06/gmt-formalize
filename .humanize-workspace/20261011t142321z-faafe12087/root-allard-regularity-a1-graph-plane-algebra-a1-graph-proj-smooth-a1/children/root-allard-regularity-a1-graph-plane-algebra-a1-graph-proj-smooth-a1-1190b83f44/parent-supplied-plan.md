# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.allard_regularity-a1.graph_plane_algebra-a1.graph_proj_smooth-a1.transpose_clm-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/nodes/root-allard-regularity-a1-graph-plane-algebra-a1-graph-proj-smooth-a1-1190b83f44/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.allard_regularity-a1.graph_plane_algebra-a1.graph_proj_smooth-a1`
- Child key: `transpose_clm`
- Declaration: `Submission.allard52_gps_transpose_exists`
- Exact Lean type: `∀ (n m : ℕ), ∃ τ : (Rn n →L[ℝ] Rn m) →L[ℝ] (Rn m →L[ℝ] Rn n), ∀ (L : Rn n →L[ℝ] Rn m) (w : Rn m) (v : Rn n), inner ℝ (τ L w) v = inner ℝ w (L v)`

## Sibling prerequisites

- None.

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
