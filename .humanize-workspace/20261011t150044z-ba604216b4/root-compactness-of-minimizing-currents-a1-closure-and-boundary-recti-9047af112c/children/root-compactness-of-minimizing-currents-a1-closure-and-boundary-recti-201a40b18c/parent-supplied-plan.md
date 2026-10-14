# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.compactness_of_minimizing_currents-a1.closure_and_boundary_rectifiability-a1.convergence_tools-a1.slice_majorant-a1.left_slope-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-compactness-of-minimizing-currents-a1-closure-and-boundary-recti-201a40b18c/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.compactness_of_minimizing_currents-a1.closure_and_boundary_rectifiability-a1.convergence_tools-a1.slice_majorant-a1`
- Child key: `left_slope`
- Declaration: `Submission.cbr_smm_liminf_left_slope_le_deriv`
- Exact Lean type: `∀ (F : ℝ → ℝ) (t : ℝ), DifferentiableAt ℝ F t → liminf (fun h : ℝ => ENNReal.ofReal h⁻¹ * ENNReal.ofReal (F t - F (t - h))) (𝓝[>] 0) ≤ ENNReal.ofReal (deriv F t)`

## Sibling prerequisites

- None.

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
