# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.dimension_reduction_results-a1.integer_density_tangent_planes-a1.cone_sector_endpoint_density-a1.rotation_conservation-a1.cone_cutoff-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-dimension-reduction-results-a1-integer-density-tangent-planes-a1-2d58dd6415/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.dimension_reduction_results-a1.integer_density_tangent_planes-a1.cone_sector_endpoint_density-a1.rotation_conservation-a1`
- Child key: `cone_cutoff`
- Declaration: `Submission.idtp_cse_rc_cone_cutoff`
- Exact Lean type: `∀ (P : ℕ) (Q : Submodule ℝ (Euclid P)) (s : ℝ), 0 < s → ∃ ζ : Euclid P → ℝ, (∀ x : Euclid P, x ≠ 0 → ContDiffAt ℝ 1 ζ x) ∧ (∀ x : Euclid P, x ≠ 0 → ‖x - Q.starProjection x‖ ≤ s / 2 * ‖x‖ → ζ x = 1) ∧ (∀ x : Euclid P, x ≠ 0 → s * ‖x‖ ≤ ‖x - Q.starProjection x‖ → ζ x = 0) ∧ (∀ x : Euclid P, x ≠ 0 → (‖x - Q.starProjection x‖ < s / 2 * ‖x‖ ∨ s * ‖x‖ < ‖x - Q.starProjection x‖) → fderiv ℝ ζ x = 0)`

## Sibling prerequisites

- None.

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
