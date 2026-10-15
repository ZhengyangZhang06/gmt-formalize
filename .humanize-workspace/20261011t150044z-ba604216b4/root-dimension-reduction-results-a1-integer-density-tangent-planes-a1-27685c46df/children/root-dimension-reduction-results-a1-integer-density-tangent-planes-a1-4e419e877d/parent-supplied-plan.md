# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.dimension_reduction_results-a1.integer_density_tangent_planes-a1.cone_sector_endpoint_density-a1.flux_density-a1.gap_ae-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-dimension-reduction-results-a1-integer-density-tangent-planes-a1-4e419e877d/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.dimension_reduction_results-a1.integer_density_tangent_planes-a1.cone_sector_endpoint_density-a1.flux_density-a1`
- Child key: `gap_ae`
- Declaration: `Submission.idtp_cse_fd_gap_ae`
- Exact Lean type: `∀ (P : ℕ) (C : GeometricCurrentOn (univ : Set (Euclid P)) 2) (Q : Submodule ℝ (Euclid P)) (a e : Euclid P) (R : IMRep (univ : Set (Euclid P)) 2) (s : ℝ), R.Represents C → 0 < s → (∀ s' : ℝ, 0 < s' → s' ≤ s → ∀ x ∈ C.support, 0 < inner ℝ x a → |‖x‖ - 1| < s' → |Real.arctan (inner ℝ x e / inner ℝ x a)| < s' → ‖x - Q.starProjection x‖ ≤ 2 * s * ‖x‖ → ‖x - Q.starProjection x‖ < s' / 4 * ‖x‖ ∧ dist x a < 3 * s') → ∀ᵐ x ∂R.measure, 0 < inner ℝ x a → |‖x‖ - 1| < s → |Real.arctan (inner ℝ x e / inner ℝ x a)| < s → ‖x - Q.starProjection x‖ < s / 2 * ‖x‖ ∨ 2 * s * ‖x‖ < ‖x - Q.starProjection x‖`

## Sibling prerequisites

- `root.half_space_cone_lies_in_boundary-a1.imrep_support_eq_measure_support-a1`

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
