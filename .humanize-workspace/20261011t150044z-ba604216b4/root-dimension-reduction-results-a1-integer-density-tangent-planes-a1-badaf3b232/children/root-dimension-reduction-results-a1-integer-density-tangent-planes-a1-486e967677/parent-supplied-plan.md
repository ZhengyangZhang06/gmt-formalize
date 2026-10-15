# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.dimension_reduction_results-a1.integer_density_tangent_planes-a1.two_dim_cone_density-a1.cone_set_finite_planes-a1.great_circle_local_plane-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-dimension-reduction-results-a1-integer-density-tangent-planes-a1-486e967677/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.dimension_reduction_results-a1.integer_density_tangent_planes-a1.two_dim_cone_density-a1.cone_set_finite_planes-a1`
- Child key: `great_circle_local_plane`
- Declaration: `Submission.idtp_tdc_csfp_great_circle_local_plane`
- Exact Lean type: `∀ (P : ℕ) (S : Set (Euclid P)) (Q : Submodule ℝ (Euclid P)) (x₀ : Euclid P) (ε₀ : ℝ), IsClosed S → (∀ p ∈ S, p ≠ 0 → ∃ (δ : ℝ) (Q' : Submodule ℝ (Euclid P)), 0 < δ ∧ Module.finrank ℝ Q' = 2 ∧ S ∩ ball p δ = (Q' : Set (Euclid P)) ∩ ball p δ) → Module.finrank ℝ Q = 2 → x₀ ∈ Q → ‖x₀‖ = 1 → 0 < ε₀ → S ∩ ball x₀ ε₀ = (Q : Set (Euclid P)) ∩ ball x₀ ε₀ → ∀ x : Euclid P, x ∈ Q → ‖x‖ = 1 → ∃ ε : ℝ, 0 < ε ∧ S ∩ ball x ε = (Q : Set (Euclid P)) ∩ ball x ε`

## Sibling prerequisites

- `root.dimension_reduction_results-a1.integer_density_tangent_planes-a1.two_dim_cone_density-a1.cone_set_finite_planes-a1.subspace_eq_of_inter_ball-a1`

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
