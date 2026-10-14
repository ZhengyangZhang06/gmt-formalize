# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.dimension_reduction_results-a1.moving_blowups-a1.deformation_theorem-a1.skeleton_deformation-a1.good_radius-a1.slice_liminf-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-dimension-reduction-results-a1-moving-blowups-a1-deformation-the-fcac1a937b/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.dimension_reduction_results-a1.moving_blowups-a1.deformation_theorem-a1.skeleton_deformation-a1.good_radius-a1`
- Child key: `slice_liminf`
- Declaration: `Submission.dimred_mbl_dtsd_gr_liminf_slice_le_deriv`
- Exact Lean type: `∀ (α : Type) [MeasurableSpace α] (μ : Measure α) (f : α → ℝ) (t : ℝ), IsFiniteMeasure μ → Measurable f → DifferentiableAt ℝ (fun s : ℝ => (μ {x | f x < s}).toReal) t → liminf (fun h : ℝ => ENNReal.ofReal h⁻¹ * μ {x | t - h < f x ∧ f x < t}) (𝓝[>] 0) ≤ ENNReal.ofReal (deriv (fun s : ℝ => (μ {x | f x < s}).toReal) t)`

## Sibling prerequisites

- `root.compactness_of_minimizing_currents-a1.closure_and_boundary_rectifiability-a1.convergence_tools-a1.slice_majorant-a1.left_slope-a1`

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
