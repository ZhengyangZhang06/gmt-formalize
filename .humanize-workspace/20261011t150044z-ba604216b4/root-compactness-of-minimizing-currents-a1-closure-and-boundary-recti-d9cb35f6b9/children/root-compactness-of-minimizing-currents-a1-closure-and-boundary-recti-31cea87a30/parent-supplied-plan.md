# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.compactness_of_minimizing_currents-a1.closure_and_boundary_rectifiability-a1.closure_compact-a1.segment_current-a1.open_segment_tangent-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-compactness-of-minimizing-currents-a1-closure-and-boundary-recti-31cea87a30/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.compactness_of_minimizing_currents-a1.closure_and_boundary_rectifiability-a1.closure_compact-a1.segment_current-a1`
- Child key: `open_segment_tangent`
- Declaration: `Submission.cbr_cc_seg_open_segment_tangent`
- Exact Lean type: `∀ (P : ℕ) (a τ : Euclid P) (ℓ : ℝ), ‖τ‖ = 1 → ∀ x ∈ (fun u : ℝ => a + u • τ) '' Ioo 0 ℓ, HasApproximateTangentSpaceAt 1 ((fun u : ℝ => a + u • τ) '' Ioo 0 ℓ) x (Submodule.span ℝ {τ})`

## Sibling prerequisites

- None.

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
