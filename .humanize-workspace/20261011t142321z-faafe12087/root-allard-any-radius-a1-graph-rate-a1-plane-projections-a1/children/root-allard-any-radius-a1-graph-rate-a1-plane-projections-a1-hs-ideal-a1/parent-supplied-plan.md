# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.allard_any_radius-a1.graph_rate-a1.plane_projections-a1.hs_ideal-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/nodes/root-allard-any-radius-a1-graph-rate-a1-plane-projections-a1-hs-ideal-a1/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.allard_any_radius-a1.graph_rate-a1.plane_projections-a1`
- Child key: `hs_ideal`
- Declaration: `Submission.any_radius_gr_pp_hs_ideal`
- Exact Lean type: `(∀ (m k : ℕ) (X : Rn m →L[ℝ] Rn k) (Y : Rn k →L[ℝ] Rn m), (∀ (u : Rn m) (v : Rn k), inner ℝ (X u) v = inner ℝ u (Y v)) → hsNormSq Y = hsNormSq X) ∧ (∀ (m k p : ℕ) (Y : Rn k →L[ℝ] Rn p) (X : Rn m →L[ℝ] Rn k), hsNormSq (Y ∘L X) ≤ ‖Y‖ ^ 2 * hsNormSq X) ∧ ∀ (m k p : ℕ) (X : Rn m →L[ℝ] Rn k) (W : Rn p →L[ℝ] Rn m), hsNormSq (X ∘L W) ≤ ‖W‖ ^ 2 * hsNormSq X`

## Sibling prerequisites

- None.

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
