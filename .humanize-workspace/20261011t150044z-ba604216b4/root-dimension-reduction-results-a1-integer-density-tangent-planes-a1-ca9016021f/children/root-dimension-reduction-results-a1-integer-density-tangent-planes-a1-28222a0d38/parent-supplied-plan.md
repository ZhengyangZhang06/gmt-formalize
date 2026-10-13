# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.dimension_reduction_results-a1.integer_density_tangent_planes-a1.two_dim_cone_density-a1.density_locally_constant-a1.light_disc-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-dimension-reduction-results-a1-integer-density-tangent-planes-a1-28222a0d38/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.dimension_reduction_results-a1.integer_density_tangent_planes-a1.two_dim_cone_density-a1.density_locally_constant-a1`
- Child key: `light_disc`
- Declaration: `Submission.idtp_tdc_dlc_light_disc`
- Exact Lean type: `∀ (P : ℕ) (C : GeometricCurrentOn (univ : Set (Euclid P)) 2) (z : Euclid P) (k : ℕ) (δ L : ℝ), IsMinimizingIn C univ → BoundaryVanishes C → IsConeCurrent C → z ∈ C.support → ‖z‖ = 1 → 1 ≤ k → 0 < δ → 0 < L → (∀ y ∈ C.support, y ∈ ball z δ → HasMassDensity C y k) → (∀ a ∈ C.support, ‖a‖ = 1 → a ∈ ball z L → HasMassDensity C a k → ∃ (δ' : ℝ) (k' : ℕ), 0 < δ' ∧ ∀ y ∈ C.support, y ∈ ball a δ' → HasMassDensity C y k') → ∃ Q : Submodule ℝ (Euclid P), Module.finrank ℝ Q = 2 ∧ z ∈ Q ∧ ∀ x ∈ (Q : Set (Euclid P)) ∩ ball z (min (1 / 2) (L / 4)), ∃ ε : ℝ, 0 < ε ∧ C.support ∩ ball x ε = (Q : Set (Euclid P)) ∩ ball x ε ∧ (∀ y ∈ C.support, y ∈ ball x ε → HasMassDensity C y k) ∧ ∀ W : Set (Euclid P), IsOpen W → W ⊆ ball x ε → μHE[2] (W ∩ (Q : Set (Euclid P))) ≤ C.massOn W`

## Sibling prerequisites

- `root.dimension_reduction_results-a1.integer_density_tangent_planes-a1.two_dim_cone_density-a1.density_locally_constant-a1.subspace_eq_of_inter_ball_eq-a1`
- `root.dimension_reduction_results-a1.integer_density_tangent_planes-a1.two_dim_cone_density-a1.density_locally_constant-a1.normalize_dist_le-a1`

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
