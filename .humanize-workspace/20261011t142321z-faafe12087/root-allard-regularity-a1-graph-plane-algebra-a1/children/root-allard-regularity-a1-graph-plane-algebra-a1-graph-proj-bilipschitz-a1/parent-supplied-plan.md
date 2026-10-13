# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.allard_regularity-a1.graph_plane_algebra-a1.graph_proj_bilipschitz-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/nodes/root-allard-regularity-a1-graph-plane-algebra-a1-graph-proj-bilipschitz-a1/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.allard_regularity-a1.graph_plane_algebra-a1`
- Child key: `graph_proj_bilipschitz`
- Declaration: `Submission.allard52_gpa_graphProj_bilipschitz`
- Exact Lean type: `∀ (n ℓ : ℕ), ∃ L₀ : ℝ, 0 < L₀ ∧ L₀ ≤ 1 / 4 ∧ ∀ (A B : Rn n →L[ℝ] Rn ℓ), hsNorm A ≤ L₀ → hsNorm B ≤ L₀ → hsNormSq (A - B) ≤ hsNormSq ((Submodule.span ℝ (Set.range fun v : Rn n => graphPoint v (A v))).starProjection - (Submodule.span ℝ (Set.range fun v : Rn n => graphPoint v (B v))).starProjection) ∧ hsNormSq ((Submodule.span ℝ (Set.range fun v : Rn n => graphPoint v (A v))).starProjection - (Submodule.span ℝ (Set.range fun v : Rn n => graphPoint v (B v))).starProjection) ≤ 3 * hsNormSq (A - B)`

## Sibling prerequisites

- `root.allard_regularity-a1.graph_plane_algebra-a1.hs_norm_bounds-a1`
- `root.allard_regularity-a1.graph_plane_algebra-a1.graph_proj_smooth-a1`

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
