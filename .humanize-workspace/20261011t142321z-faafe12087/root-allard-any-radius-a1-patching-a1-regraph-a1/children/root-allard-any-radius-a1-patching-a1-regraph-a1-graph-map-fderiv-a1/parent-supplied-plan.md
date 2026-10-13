# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.allard_any_radius-a1.patching-a1.regraph-a1.graph_map_fderiv-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/nodes/root-allard-any-radius-a1-patching-a1-regraph-a1-graph-map-fderiv-a1/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.allard_any_radius-a1.patching-a1.regraph-a1`
- Child key: `graph_map_fderiv`
- Declaration: `Submission.arp_rgr_graph_map_fderiv`
- Exact Lean type: `∀ {n ℓ : ℕ} (q : Amb n ℓ ≃ₗᵢ[ℝ] Amb n ℓ) (v : Rn n → Rn ℓ) (y : Amb n ℓ) (U : Set (Rn n)), IsOpen U → ContDiffOn ℝ 1 v U → ContDiffOn ℝ 1 (fun x => y + q (graphPoint x (v x))) U ∧ ∀ x ∈ U, ∀ h : Rn n, fderiv ℝ (fun x => y + q (graphPoint x (v x))) x h = q (graphPoint h (fderiv ℝ v x h))`

## Sibling prerequisites

- None.

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
