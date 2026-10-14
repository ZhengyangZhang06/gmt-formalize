# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.compactness_of_minimizing_currents-a1.closure_and_boundary_rectifiability-a1.closure_compact-a1.segment_current-a1.line_hausdorff-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-compactness-of-minimizing-currents-a1-closure-and-boundary-recti-48c294623d/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.compactness_of_minimizing_currents-a1.closure_and_boundary_rectifiability-a1.closure_compact-a1.segment_current-a1`
- Child key: `line_hausdorff`
- Declaration: `Submission.cbr_cc_seg_line_hausdorff`
- Exact Lean type: `∀ (P : ℕ) (a τ : Euclid P), ‖τ‖ = 1 → ∀ A : Set ℝ, MeasurableSet A → MeasurableSet ((fun u : ℝ => a + u • τ) '' A) ∧ μHE[1] ((fun u : ℝ => a + u • τ) '' A) = volume A ∧ ∀ h : Euclid P → ℝ, ∫ x in (fun u : ℝ => a + u • τ) '' A, h x ∂μHE[1] = ∫ u in A, h (a + u • τ)`

## Sibling prerequisites

- None.

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
