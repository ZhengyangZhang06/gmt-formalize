# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.dimension_reduction_results-a1.integer_density_tangent_planes-a1.cone_sector_endpoint_density-a1.rotation_conservation-a1.test_function-a1.support_bound-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-dimension-reduction-results-a1-integer-density-tangent-planes-a1-b2be5bd7b2/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.dimension_reduction_results-a1.integer_density_tangent_planes-a1.cone_sector_endpoint_density-a1.rotation_conservation-a1.test_function-a1`
- Child key: `support_bound`
- Declaration: `Submission.idtp_cse_rc_tf_support_bound`
- Exact Lean type: `∀ (P : ℕ) (Q : Submodule ℝ (Euclid P)) (a e y : Euclid P) (s : ℝ), 0 < s → s ≤ 1 / 4 → ‖Q.starProjection y‖ ^ 2 = inner ℝ y a ^ 2 + inner ℝ y e ^ 2 → 0 < inner ℝ y a → |‖y‖ - 1| < s → |Real.arctan (inner ℝ y e / inner ℝ y a)| < s → ‖y - Q.starProjection y‖ < s * ‖y‖ → 1 / 2 < inner ℝ y a ∧ ‖y‖ < 5 / 4`

## Sibling prerequisites

- None.

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
