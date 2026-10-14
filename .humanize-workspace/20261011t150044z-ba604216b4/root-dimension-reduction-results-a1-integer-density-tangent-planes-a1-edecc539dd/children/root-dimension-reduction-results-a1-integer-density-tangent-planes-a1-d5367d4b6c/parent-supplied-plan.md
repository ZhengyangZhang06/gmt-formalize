# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.dimension_reduction_results-a1.integer_density_tangent_planes-a1.two_dim_cone_density-a1.no_infinite_planar_pieces-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-dimension-reduction-results-a1-integer-density-tangent-planes-a1-d5367d4b6c/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.dimension_reduction_results-a1.integer_density_tangent_planes-a1.two_dim_cone_density-a1`
- Child key: `no_infinite_planar_pieces`
- Declaration: `Submission.idtp_tdc_no_infinite_planar_pieces`
- Exact Lean type: `∀ (P : ℕ) (C : GeometricCurrentOn (univ : Set (Euclid P)) 2) (Q : ℕ → Submodule ℝ (Euclid P)) (z : ℕ → Euclid P) (ρ R : ℝ), IsIntegerMultiplicity C → 0 < ρ → (∀ i, Module.finrank ℝ (Q i) = 2) → (∀ i, z i ∈ Q i) → (∀ i, ‖z i‖ ≤ R) → (∀ i j, i ≠ j → Disjoint ((Q i : Set (Euclid P)) ∩ ball (z i) ρ) ((Q j : Set (Euclid P)) ∩ ball (z j) ρ)) → (∀ i, ∀ w ∈ (Q i : Set (Euclid P)) ∩ ball (z i) ρ, ∃ ε : ℝ, 0 < ε ∧ ∀ W : Set (Euclid P), IsOpen W → W ⊆ ball w ε → μHE[2] (W ∩ (Q i : Set (Euclid P))) ≤ C.massOn W) → False`

## Sibling prerequisites

- `root.dimension_reduction_results-a1.integer_density_tangent_planes-a1.two_dim_cone_density-a1.subspace_ball_measure-a1`

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
