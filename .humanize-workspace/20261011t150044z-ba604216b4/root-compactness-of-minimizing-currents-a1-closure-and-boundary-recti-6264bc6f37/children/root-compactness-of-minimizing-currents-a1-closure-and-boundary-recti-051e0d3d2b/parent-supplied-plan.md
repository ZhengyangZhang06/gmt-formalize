# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.compactness_of_minimizing_currents-a1.closure_and_boundary_rectifiability-a1.cycle_im-a1.blowup_limit-a1.rescaled_bounds-a1.null_seq_transfer-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-compactness-of-minimizing-currents-a1-closure-and-boundary-recti-051e0d3d2b/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.compactness_of_minimizing_currents-a1.closure_and_boundary_rectifiability-a1.cycle_im-a1.blowup_limit-a1.rescaled_bounds-a1`
- Child key: `null_seq_transfer`
- Declaration: `Submission.cbr_ci_bl_rb_null_seq_transfer`
- Exact Lean type: `∀ (f h : ℝ → ℝ≥0∞) (C : ℝ≥0∞) (s : ℕ → ℝ), C ≠ ∞ → (∀ i, 0 < s i) → Tendsto s atTop (𝓝 0) → (limsup f (𝓝[>] 0) ≤ 1 → limsup (fun i => C * f (s i)) atTop ≤ C) ∧ (Tendsto h (𝓝[>] 0) (𝓝 0) → Tendsto (fun i => C * h (s i)) atTop (𝓝 0))`

## Sibling prerequisites

- None.

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
