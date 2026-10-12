# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.allard_any_radius-a1.graph_rate-a1.plane_projections-a1.hs_proj_split-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/nodes/root-allard-any-radius-a1-graph-rate-a1-plane-projections-a1-hs-proj-split-a1/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.allard_any_radius-a1.graph_rate-a1.plane_projections-a1`
- Child key: `hs_proj_split`
- Declaration: `Submission.any_radius_gr_pp_hs_proj_split`
- Exact Lean type: `(∀ (m k : ℕ) (X : Rn m →L[ℝ] Rn k) (K : Submodule ℝ (Rn m)), hsNormSq X = hsNormSq (X ∘L K.starProjection) + hsNormSq (X ∘L Kᗮ.starProjection)) ∧ ∀ (m : ℕ) (K L : Submodule ℝ (Rn m)), hsNormSq (K.starProjection - L.starProjection) = hsNormSq ((K.starProjection - L.starProjection) ∘L K.starProjection) + hsNormSq ((K.starProjection - L.starProjection) ∘L L.starProjection)`

## Sibling prerequisites

- `root.allard_any_radius-a1.graph_rate-a1.plane_projections-a1.hs_ideal-a1`

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
