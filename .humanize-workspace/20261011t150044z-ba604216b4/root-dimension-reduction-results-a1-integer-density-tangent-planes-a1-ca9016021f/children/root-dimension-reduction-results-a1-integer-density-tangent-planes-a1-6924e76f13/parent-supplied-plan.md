# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.dimension_reduction_results-a1.integer_density_tangent_planes-a1.two_dim_cone_density-a1.density_locally_constant-a1.accumulating_discs-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-dimension-reduction-results-a1-integer-density-tangent-planes-a1-6924e76f13/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.dimension_reduction_results-a1.integer_density_tangent_planes-a1.two_dim_cone_density-a1.density_locally_constant-a1`
- Child key: `accumulating_discs`
- Declaration: `Submission.idtp_tdc_dlc_accumulating_discs`
- Exact Lean type: `∀ (P : ℕ) (C : GeometricCurrentOn (univ : Set (Euclid P)) 2) (Q : ℕ → Submodule ℝ (Euclid P)) (z : ℕ → Euclid P) (k : ℕ → ℕ) (b : Euclid P) (ρ : ℝ), IsIntegerMultiplicity C → 0 < ρ → (∀ i, Module.finrank ℝ (Q i) = 2) → (∀ i, z i ∈ Q i) → Tendsto z atTop (𝓝 b) → (∀ i, ∀ x ∈ (Q i : Set (Euclid P)) ∩ ball (z i) ρ, ∃ ε : ℝ, 0 < ε ∧ C.support ∩ ball x ε = (Q i : Set (Euclid P)) ∩ ball x ε ∧ (∀ y ∈ C.support, y ∈ ball x ε → HasMassDensity C y (k i)) ∧ ∀ W : Set (Euclid P), IsOpen W → W ⊆ ball x ε → μHE[2] (W ∩ (Q i : Set (Euclid P))) ≤ C.massOn W) → (¬ ∃ (ε : ℝ) (m : ℕ), 0 < ε ∧ ∀ y ∈ C.support, y ∈ ball b ε → HasMassDensity C y m) → False`

## Sibling prerequisites

- `root.dimension_reduction_results-a1.integer_density_tangent_planes-a1.two_dim_cone_density-a1.density_locally_constant-a1.subspace_eq_of_inter_ball_eq-a1`

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
