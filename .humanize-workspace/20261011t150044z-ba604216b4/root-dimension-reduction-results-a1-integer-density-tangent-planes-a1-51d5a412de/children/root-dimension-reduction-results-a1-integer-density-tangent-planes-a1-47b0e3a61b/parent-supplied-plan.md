# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.dimension_reduction_results-a1.integer_density_tangent_planes-a1.cone_sector_endpoint_density-a1.edge_tangent_plane-a1.localization-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-dimension-reduction-results-a1-integer-density-tangent-planes-a1-47b0e3a61b/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.dimension_reduction_results-a1.integer_density_tangent_planes-a1.cone_sector_endpoint_density-a1.edge_tangent_plane-a1`
- Child key: `localization`
- Declaration: `Submission.idtp_cse_etp_localization`
- Exact Lean type: `∀ (P : ℕ) (Q : Submodule ℝ (Euclid P)) (a e : Euclid P) (Z : Set (Euclid P)) (s₁ : ℝ), Module.finrank ℝ Q = 2 → a ∈ Q → e ∈ Q → ‖a‖ = 1 → ‖e‖ = 1 → inner ℝ a e = 0 → 0 < s₁ → (∀ x ∈ Z, dist x a < s₁ → ‖x - Q.starProjection x‖ ≤ 1 / 20 * dist x a) → ∃ s₀ : ℝ, 0 < s₀ ∧ s₀ ≤ 1 / 4 ∧ (∀ s' : ℝ, 0 < s' → s' ≤ s₀ → ∀ x ∈ Z, 0 < inner ℝ x a → |‖x‖ - 1| < s' → |Real.arctan (inner ℝ x e / inner ℝ x a)| < s' → ‖x - Q.starProjection x‖ ≤ 2 * s₀ * ‖x‖ → ‖x - Q.starProjection x‖ < s' / 4 * ‖x‖ ∧ dist x a < 3 * s')`

## Sibling prerequisites

- None.

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
