# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.allard_regularity-a1.graph_plane_algebra-a1.rotation_exists-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/nodes/root-allard-regularity-a1-graph-plane-algebra-a1-rotation-exists-a1/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.allard_regularity-a1.graph_plane_algebra-a1`
- Child key: `rotation_exists`
- Declaration: `Submission.allard52_gpa_exists_rotatedPlane_eq`
- Exact Lean type: `∀ (n ℓ : ℕ) (T : Submodule ℝ (Amb n ℓ)), Module.finrank ℝ T = n → ∃ q : Amb n ℓ ≃ₗᵢ[ℝ] Amb n ℓ, rotatedPlane q = T`

## Sibling prerequisites

- None.

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
