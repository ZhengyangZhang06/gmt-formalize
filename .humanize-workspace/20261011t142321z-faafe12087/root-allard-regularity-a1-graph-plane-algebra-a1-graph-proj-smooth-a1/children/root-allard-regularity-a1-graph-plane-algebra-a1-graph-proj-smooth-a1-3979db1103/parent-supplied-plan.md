# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.allard_regularity-a1.graph_plane_algebra-a1.graph_proj_smooth-a1.gram_projection-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/nodes/root-allard-regularity-a1-graph-plane-algebra-a1-graph-proj-smooth-a1-3979db1103/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.allard_regularity-a1.graph_plane_algebra-a1.graph_proj_smooth-a1`
- Child key: `gram_projection`
- Declaration: `Submission.allard52_gps_starProjection_eq_gram`
- Exact Lean type: `∀ (n ℓ : ℕ) (A : Rn n →L[ℝ] Rn ℓ) (J : Rn n →L[ℝ] Amb n ℓ) (T : Amb n ℓ →L[ℝ] Rn n), (∀ v : Rn n, J v = graphPoint v (A v)) → (∀ (w : Amb n ℓ) (v : Rn n), inner ℝ (T w) v = inner ℝ w (J v)) → IsUnit (T ∘L J) ∧ (Submodule.span ℝ (Set.range fun v : Rn n => graphPoint v (A v))).starProjection = J ∘L Ring.inverse (T ∘L J) ∘L T`

## Sibling prerequisites

- None.

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
