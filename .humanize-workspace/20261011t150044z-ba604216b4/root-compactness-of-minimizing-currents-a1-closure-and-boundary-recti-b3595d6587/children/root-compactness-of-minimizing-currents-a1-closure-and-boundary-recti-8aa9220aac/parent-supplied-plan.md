# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.compactness_of_minimizing_currents-a1.closure_and_boundary_rectifiability-a1.cycle_im-a1.constant_planes-a1.finite_planes-a1.total_weight-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-compactness-of-minimizing-currents-a1-closure-and-boundary-recti-8aa9220aac/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.compactness_of_minimizing_currents-a1.closure_and_boundary_rectifiability-a1.cycle_im-a1.constant_planes-a1.finite_planes-a1`
- Child key: `total_weight`
- Declaration: `Submission.cbr_ci_cp_fp_tsum_weight_le_one`
- Exact Lean type: `∀ (P n : ℕ) (ν : Measure (Euclid P)) (V : Submodule ℝ (Euclid P)) (Z : Set (Euclid P)) (a : Euclid P → ℝ≥0∞), Module.finrank ℝ V = n → Z ⊆ (Vᗮ : Set (Euclid P)) → ν = Measure.sum (fun w : Z => a w • (μHE[n]).restrict {y : Euclid P | y - w ∈ V}) → (∀ R : ℝ, 0 < R → ν (ball 0 R) ≤ unitBallVolume n * ENNReal.ofReal (R ^ n)) → ∑' w : Z, a w ≤ 1`

## Sibling prerequisites

- `root.compactness_of_minimizing_currents-a1.closure_and_boundary_rectifiability-a1.cycle_im-a1.constant_planes-a1.finite_planes-a1.plane_ball-a1`

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
