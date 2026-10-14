# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.dimension_reduction_results-a1.integer_density_tangent_planes-a1.flat_off_null_set-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-dimension-reduction-results-a1-integer-density-tangent-planes-a1-4fcbfb5d62/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.dimension_reduction_results-a1.integer_density_tangent_planes-a1`
- Child key: `flat_off_null_set`
- Declaration: `Submission.idtp_flat_off_null_set`
- Exact Lean type: `∀ (n k ℓ : ℕ), ℓ ≤ k → ∀ (U N : Set (Euclid (n + k))) (T : GeometricCurrentOn U n), 1 ≤ n → IsOpen U → IsEmbeddedSubmanifold 2 (n + ℓ) N → (closure N \ N) ∩ U = ∅ → IsMinimizingIn T (U ∩ N) → T.support ⊆ U ∩ N → BoundaryVanishes T → ∃ F : Set (Euclid (n + k)), (∀ α : ℝ, 0 < α → μH[(n : ℝ) - 2 + α] F = 0) ∧ ∀ x ∈ T.support \ F, ∀ β : ℝ, 0 < β → ∀ R : ℝ, 0 < R → ∃ ρ : ℝ, 0 < ρ ∧ ρ < R ∧ ∃ Q : Submodule ℝ (Euclid (n + k)), Module.finrank ℝ Q = n ∧ ∀ y ∈ T.support, dist y x < ρ → ‖(y - x) - Q.starProjection (y - x)‖ < β * ρ`

## Sibling prerequisites

- `root.dimension_reduction_results-a1.integer_density_tangent_planes-a1.weak_limit_mass_bound-a1`
- `root.dimension_reduction_results-a1.integer_density_tangent_planes-a1.density_eq_multiplicity_ae-a1`

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
