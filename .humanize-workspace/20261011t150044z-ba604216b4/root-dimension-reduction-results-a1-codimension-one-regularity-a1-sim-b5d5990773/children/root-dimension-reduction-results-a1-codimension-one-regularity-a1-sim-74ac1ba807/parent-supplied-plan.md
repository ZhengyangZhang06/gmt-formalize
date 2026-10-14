# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.dimension_reduction_results-a1.codimension_one_regularity-a1.simons_regular_cone-a1.hypercone_plane-a1.stability-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-dimension-reduction-results-a1-codimension-one-regularity-a1-sim-74ac1ba807/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.dimension_reduction_results-a1.codimension_one_regularity-a1.simons_regular_cone-a1.hypercone_plane-a1`
- Child key: `stability`
- Declaration: `Submission.codim1_hcp_stability_inequality`
- Exact Lean type: `∀ (P m : ℕ) (U : Set (Euclid P)) (A₀ : Submodule ℝ (Euclid P)) (M : Set (Euclid P)) (ν : Euclid P → Euclid P), IsOpen U → M ⊆ U → Module.finrank ℝ A₀ = m + 1 → M ⊆ (A₀ : Set (Euclid P)) → (∀ r : ℕ, IsEmbeddedSubmanifold r m M) → (∀ K : Set (Euclid P), IsCompact K → K ⊆ U → μHE[m] (M ∩ K) ≠ ∞) → (∃ O : Set (Euclid P), IsOpen O ∧ M ⊆ O ∧ ContDiffOn ℝ (⊤ : ℕ∞) ν O) → (∀ x ∈ M, ν x ∈ A₀ ∧ ‖ν x‖ = 1 ∧ ∀ v ∈ tangentSpace M x, inner ℝ (ν x) v = 0) → (∀ x ∈ M, LinearMap.trace ℝ (Euclid P) ((Submodule.span ℝ (tangentSpace M x)).starProjection.toLinearMap ∘ₗ (fderiv ℝ ν x).toLinearMap) = 0) → (∀ Z : Euclid P → Euclid P, ContDiff ℝ (⊤ : ℕ∞) Z → HasCompactSupport Z → tsupport Z ⊆ U → ∃ t₀ : ℝ, 0 < t₀ ∧ ∀ t : ℝ, |t| < t₀ → μHE[m] (M ∩ tsupport Z) ≤ μHE[m] ((fun x => x + t • Z x) '' (M ∩ tsupport Z))) → ∀ ζ : Euclid P → ℝ, LocallyLipschitzOn M ζ → (∃ C : Set (Euclid P), IsCompact C ∧ C ⊆ M ∧ ∀ x ∈ M, x ∉ C → ζ x = 0) → ∫ x in M, (∑ j : Fin P, ‖fderiv ℝ ν x ((Submodule.span ℝ (tangentSpace M x)).starProjection (EuclideanSpace.single j 1))‖ ^ 2) * ζ x ^ 2 ∂μHE[m] ≤ ∫ x in M, ∑ j : Fin P, (fderivWithin ℝ ζ M x ((Submodule.span ℝ (tangentSpace M x)).starProjection (EuclideanSpace.single j 1))) ^ 2 ∂μHE[m]`

## Sibling prerequisites

- `root.dimension_reduction_results-a1.codimension_one_regularity-a1.simons_regular_cone-a1.hypercone_plane-a1.area_formula-a1`
- `root.dimension_reduction_results-a1.codimension_one_regularity-a1.simons_regular_cone-a1.hypercone_plane-a1.lipschitz_approx-a1`
- `root.dimension_reduction_results-a1.codimension_one_regularity-a1.simons_regular_cone-a1.hypercone_plane-a1.smooth_charts-a1`
- `root.minimizing_implies_stationary-a1.chart_tangent_space-a1`
- `root.dimension_reduction_results-a1.regular_point_density-a1.locally_closed-a1`

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
