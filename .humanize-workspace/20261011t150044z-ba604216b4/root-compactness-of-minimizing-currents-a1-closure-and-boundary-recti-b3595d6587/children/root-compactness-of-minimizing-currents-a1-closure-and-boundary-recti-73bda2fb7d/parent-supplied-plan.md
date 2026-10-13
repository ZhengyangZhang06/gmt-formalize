# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.compactness_of_minimizing_currents-a1.closure_and_boundary_rectifiability-a1.cycle_im-a1.constant_planes-a1.finite_planes-a1.plane_ball-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-compactness-of-minimizing-currents-a1-closure-and-boundary-recti-73bda2fb7d/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.compactness_of_minimizing_currents-a1.closure_and_boundary_rectifiability-a1.cycle_im-a1.constant_planes-a1.finite_planes-a1`
- Child key: `plane_ball`
- Declaration: `Submission.cbr_ci_cp_fp_offset_plane_ball_measure`
- Exact Lean type: `∀ (P n : ℕ) (V : Submodule ℝ (Euclid P)) (w : Euclid P) (R : ℝ), Module.finrank ℝ V = n → w ∈ Vᗮ → ‖w‖ < R → μHE[n] ({y : Euclid P | y - w ∈ V} ∩ ball 0 R) = unitBallVolume n * ENNReal.ofReal (Real.sqrt (R ^ 2 - ‖w‖ ^ 2) ^ n)`

## Sibling prerequisites

- `root.dimension_reduction_results-a1.integer_density_tangent_planes-a1.two_dim_cone_density-a1.subspace_ball_measure-a1`

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
