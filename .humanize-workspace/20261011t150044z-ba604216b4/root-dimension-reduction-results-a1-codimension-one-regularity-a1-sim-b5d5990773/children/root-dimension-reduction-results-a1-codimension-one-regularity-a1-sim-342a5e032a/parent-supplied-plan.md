# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.dimension_reduction_results-a1.codimension_one_regularity-a1.simons_regular_cone-a1.hypercone_plane-a1.unit_normal-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-dimension-reduction-results-a1-codimension-one-regularity-a1-sim-342a5e032a/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.dimension_reduction_results-a1.codimension_one_regularity-a1.simons_regular_cone-a1.hypercone_plane-a1`
- Child key: `unit_normal`
- Declaration: `Submission.codim1_hcp_minimal_unit_normal`
- Exact Lean type: `∀ (P m : ℕ) (U : Set (Euclid P)) (A₀ : Submodule ℝ (Euclid P)) (M : Set (Euclid P)), IsOpen U → M ⊆ U → Module.finrank ℝ A₀ = m + 1 → M ⊆ (A₀ : Set (Euclid P)) → (∀ r : ℕ, IsEmbeddedSubmanifold r m M) → (∃ ξ : Euclid P → MultiVector P m, IsOrientation m M ξ) → (∀ K : Set (Euclid P), IsCompact K → K ⊆ U → μHE[m] (M ∩ K) ≠ ∞) → (∀ X : Euclid P → Euclid P, ContDiff ℝ 1 X → HasCompactSupport X → tsupport X ⊆ U → ∫ x in M, LinearMap.trace ℝ (Euclid P) ((Submodule.span ℝ (tangentSpace M x)).starProjection.toLinearMap ∘ₗ (fderiv ℝ X x).toLinearMap) ∂μHE[m] = 0) → ∃ (ν : Euclid P → Euclid P) (O : Set (Euclid P)), IsOpen O ∧ M ⊆ O ∧ ContDiffOn ℝ (⊤ : ℕ∞) ν O ∧ (∀ x ∈ M, ν x ∈ A₀ ∧ ‖ν x‖ = 1 ∧ ∀ v ∈ tangentSpace M x, inner ℝ (ν x) v = 0) ∧ ∀ x ∈ M, LinearMap.trace ℝ (Euclid P) ((Submodule.span ℝ (tangentSpace M x)).starProjection.toLinearMap ∘ₗ (fderiv ℝ ν x).toLinearMap) = 0`

## Sibling prerequisites

- `root.dimension_reduction_results-a1.codimension_one_regularity-a1.simons_regular_cone-a1.hypercone_plane-a1.smooth_charts-a1`
- `root.minimizing_implies_stationary-a1.chart_tangent_space-a1`
- `root.dimension_reduction_results-a1.regular_point_density-a1.density_one-a1`
- `root.dimension_reduction_results-a1.regular_point_density-a1.locally_closed-a1`

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
