# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.dimension_reduction_results-a1.integer_density_tangent_planes-a1.cone_sector_endpoint_density-a1.rotation_conservation-a1.test_function-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-dimension-reduction-results-a1-integer-density-tangent-planes-a1-db9ae3fc33/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.dimension_reduction_results-a1.integer_density_tangent_planes-a1.cone_sector_endpoint_density-a1.rotation_conservation-a1`
- Child key: `test_function`
- Declaration: `Submission.idtp_cse_rc_test_function`
- Exact Lean type: `∀ (P : ℕ) (Q : Submodule ℝ (Euclid P)) (a e : Euclid P) (s : ℝ) (ψ l : ℝ → ℝ), Module.finrank ℝ Q = 2 → a ∈ Q → e ∈ Q → ‖a‖ = 1 → ‖e‖ = 1 → inner ℝ a e = 0 → 0 < s → s ≤ 1 / 4 → ContDiff ℝ 1 ψ → ContDiff ℝ 1 l → tsupport ψ ⊆ Ioo (-s) s → tsupport l ⊆ Ioo (1 - s) (1 + s) → ∃ g : Euclid P → ℝ, ContDiff ℝ 1 g ∧ HasCompactSupport g ∧ (∀ x v : Euclid P, inner ℝ x v = 0 → (0 < inner ℝ x a → |‖x‖ - 1| < s → |Real.arctan (inner ℝ x e / inner ℝ x a)| < s → ‖x - Q.starProjection x‖ < s / 2 * ‖x‖ ∨ 2 * s * ‖x‖ < ‖x - Q.starProjection x‖) → x ∈ {y : Euclid P | 0 < inner ℝ y a ∧ |‖y‖ - 1| < s ∧ |Real.arctan (inner ℝ y e / inner ℝ y a)| < s ∧ ‖y - Q.starProjection y‖ < s * ‖y‖} → fderiv ℝ g x v = deriv ψ (Real.arctan (inner ℝ x e / inner ℝ x a)) * l ‖x‖ * (inner ℝ (inner ℝ x a • e - inner ℝ x e • a) v / ‖Q.starProjection x‖ ^ 2)) ∧ (∀ x v : Euclid P, inner ℝ x v = 0 → (0 < inner ℝ x a → |‖x‖ - 1| < s → |Real.arctan (inner ℝ x e / inner ℝ x a)| < s → ‖x - Q.starProjection x‖ < s / 2 * ‖x‖ ∨ 2 * s * ‖x‖ < ‖x - Q.starProjection x‖) → x ∉ {y : Euclid P | 0 < inner ℝ y a ∧ |‖y‖ - 1| < s ∧ |Real.arctan (inner ℝ y e / inner ℝ y a)| < s ∧ ‖y - Q.starProjection y‖ < s * ‖y‖} → fderiv ℝ g x v = 0)`

## Sibling prerequisites

- `root.dimension_reduction_results-a1.integer_density_tangent_planes-a1.cone_sector_endpoint_density-a1.rotation_conservation-a1.cone_cutoff-a1`
- `root.dimension_reduction_results-a1.integer_density_tangent_planes-a1.cone_sector_endpoint_density-a1.rotation_conservation-a1.angle_fderiv-a1`

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
