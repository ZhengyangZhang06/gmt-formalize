# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.density_one_higher_regularity-a1.elliptic_bootstrap-a1.linear_higher_regularity-a1.dq_uniform_bounds-a1.dq_mean_value-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/nodes/root-density-one-higher-regularity-a1-elliptic-bootstrap-a1-linear-hi-95dc916fc0/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.density_one_higher_regularity-a1.elliptic_bootstrap-a1.linear_higher_regularity-a1.dq_uniform_bounds-a1`
- Child key: `dq_mean_value`
- Declaration: `Submission.dohr_eb_lhr_dqub_dq_mean_value`
- Exact Lean type: `∀ (E F : Type) [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F] (α : ℝ) (U : Set E) (g : E → F) (xb e : E) (R S H d : ℝ), IsOpen U → closedBall xb (4 * R) ⊆ U → ‖e‖ ≤ 1 → DifferentiableOn ℝ g U → (∀ z ∈ closedBall xb (4 * R), ‖fderiv ℝ g z‖ ≤ S) → (∀ z ∈ closedBall xb (4 * R), ∀ w ∈ closedBall xb (4 * R), ‖fderiv ℝ g z - fderiv ℝ g w‖ ≤ H * ‖z - w‖ ^ α) → d ≠ 0 → |d| < R → ∀ x ∈ ball xb (2 * R), ∀ y ∈ ball xb (2 * R), ‖d⁻¹ • (g (x + d • e) - g x)‖ ≤ S ∧ ‖d⁻¹ • (g (x + d • e) - g x) - d⁻¹ • (g (y + d • e) - g y)‖ ≤ H * ‖x - y‖ ^ α`

## Sibling prerequisites

- None.

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
