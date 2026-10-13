# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.dimension_reduction_results-a1.integer_density_tangent_planes-a1.integer_density-a1.local_threshold_null-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-dimension-reduction-results-a1-integer-density-tangent-planes-a1-fd0ec201c9/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.dimension_reduction_results-a1.integer_density_tangent_planes-a1.integer_density-a1`
- Child key: `local_threshold_null`
- Declaration: `Submission.idod_local_threshold_null`
- Exact Lean type: `∀ (n k ℓ : ℕ), ℓ ≤ k → ∀ (U N : Set (Euclid (n + k))) (T : GeometricCurrentOn U n), 1 ≤ n → IsOpen U → IsEmbeddedSubmanifold 2 (n + ℓ) N → (closure N \ N) ∩ U = ∅ → IsMinimizingIn T (U ∩ N) → T.support ⊆ U ∩ N → BoundaryVanishes T → ∀ (m : ℕ) (β σ : ℝ) (x₀ : Euclid (n + k)), 1 ≤ m → 0 < β → 0 < σ → closedBall x₀ (4 * σ) ⊆ U → (∀ y ∈ closedBall x₀ (4 * σ), ∃ θ : ℝ, θ < (m : ℝ) - β ∧ HasMassDensity T y θ) → ∀ α : ℝ, 0 < α → μH[(n : ℝ) - 3 + α] {x | x ∈ ball x₀ σ ∧ ∃ θ : ℝ, (m : ℝ) - 1 + β ≤ θ ∧ HasMassDensity T x θ} = 0`

## Sibling prerequisites

- `root.dimension_reduction_results-a1.integer_density_tangent_planes-a1.integer_density-a1.uniform_density_bound-a1`
- `root.dimension_reduction_results-a1.integer_density_tangent_planes-a1.integer_density-a1.limit_density_bound-a1`
- `root.dimension_reduction_results-a1.integer_density_tangent_planes-a1.integer_density-a1.planar_density_integer-a1`
- `root.dimension_reduction_results-a1.integer_density_tangent_planes-a1.integer_density-a1.spine_density_integer-a1`

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
