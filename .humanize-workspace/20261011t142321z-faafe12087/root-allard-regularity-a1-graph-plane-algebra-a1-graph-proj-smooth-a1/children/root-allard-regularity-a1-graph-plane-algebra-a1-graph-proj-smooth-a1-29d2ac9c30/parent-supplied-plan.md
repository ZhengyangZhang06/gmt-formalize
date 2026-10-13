# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.allard_regularity-a1.graph_plane_algebra-a1.graph_proj_smooth-a1.proj_fderiv_zero-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/nodes/root-allard-regularity-a1-graph-plane-algebra-a1-graph-proj-smooth-a1-29d2ac9c30/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.allard_regularity-a1.graph_plane_algebra-a1.graph_proj_smooth-a1`
- Child key: `proj_fderiv_zero`
- Declaration: `Submission.allard52_gps_fderiv_zero_apply`
- Exact Lean type: `∀ (n ℓ : ℕ) (H : Rn n →L[ℝ] Rn ℓ) (x : Rn n) (y : Rn ℓ), fderiv ℝ (fun A : Rn n →L[ℝ] Rn ℓ => (Submodule.span ℝ (Set.range fun v : Rn n => graphPoint v (A v))).starProjection) 0 H (graphPoint x y) = graphPoint (∑ i : Fin n, inner ℝ (H (EuclideanSpace.single i 1)) y • EuclideanSpace.single i 1) (H x)`

## Sibling prerequisites

- `root.allard_regularity-a1.graph_plane_algebra-a1.graph_proj_smooth-a1.transpose_clm-a1`
- `root.allard_regularity-a1.graph_plane_algebra-a1.graph_proj_smooth-a1.gram_projection-a1`

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
