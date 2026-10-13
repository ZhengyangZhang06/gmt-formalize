# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.dimension_reduction_results-a1.integer_density_tangent_planes-a1.two_dim_cone_density-a1.cone_set_finite_planes-a1.planes_eq_or_inf_bot-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-dimension-reduction-results-a1-integer-density-tangent-planes-a1-aa49a3fc64/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.dimension_reduction_results-a1.integer_density_tangent_planes-a1.two_dim_cone_density-a1.cone_set_finite_planes-a1`
- Child key: `planes_eq_or_inf_bot`
- Declaration: `Submission.idtp_tdc_csfp_planes_eq_or_inf_bot`
- Exact Lean type: `∀ (P : ℕ) (S : Set (Euclid P)) (Q₁ Q₂ : Submodule ℝ (Euclid P)) (p₁ p₂ : Euclid P) (δ₁ δ₂ : ℝ), IsClosed S → (∀ p ∈ S, p ≠ 0 → ∃ (δ : ℝ) (Q : Submodule ℝ (Euclid P)), 0 < δ ∧ Module.finrank ℝ Q = 2 ∧ S ∩ ball p δ = (Q : Set (Euclid P)) ∩ ball p δ) → Module.finrank ℝ Q₁ = 2 → Module.finrank ℝ Q₂ = 2 → p₁ ∈ Q₁ → ‖p₁‖ = 1 → 0 < δ₁ → S ∩ ball p₁ δ₁ = (Q₁ : Set (Euclid P)) ∩ ball p₁ δ₁ → p₂ ∈ Q₂ → ‖p₂‖ = 1 → 0 < δ₂ → S ∩ ball p₂ δ₂ = (Q₂ : Set (Euclid P)) ∩ ball p₂ δ₂ → Q₁ = Q₂ ∨ Q₁ ⊓ Q₂ = ⊥`

## Sibling prerequisites

- `root.dimension_reduction_results-a1.integer_density_tangent_planes-a1.two_dim_cone_density-a1.cone_set_finite_planes-a1.subspace_eq_of_inter_ball-a1`
- `root.dimension_reduction_results-a1.integer_density_tangent_planes-a1.two_dim_cone_density-a1.cone_set_finite_planes-a1.great_circle_local_plane-a1`

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
