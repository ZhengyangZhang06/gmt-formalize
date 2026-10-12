# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.lipschitz_graph_corollary-a1.hole_estimate-a1.hs_norm_bounds-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/nodes/root-lipschitz-graph-corollary-a1-hole-estimate-a1-hs-norm-bounds-a1/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.lipschitz_graph_corollary-a1.hole_estimate-a1`
- Child key: `hs_norm_bounds`
- Declaration: `Submission.lgc_hsNormSq_bounds`
- Exact Lean type: `∀ (m k : ℕ), Continuous (fun A : Rn m →L[ℝ] Rn k => hsNormSq A) ∧ ∀ A : Rn m →L[ℝ] Rn k, 0 ≤ hsNormSq A ∧ hsNormSq A ≤ m * ‖A‖ ^ 2 ∧ ∀ v : Rn m, ‖A v‖ ^ 2 ≤ hsNormSq A * ‖v‖ ^ 2`

## Sibling prerequisites

- None.

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
