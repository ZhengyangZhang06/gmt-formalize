# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.dimension_reduction_results-a1.codimension_one_regularity-a1.simons_regular_cone-a1.hypercone_plane-a1.first_variation-a1.smooth_to_c1-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-dimension-reduction-results-a1-codimension-one-regularity-a1-sim-c82f8e44f4/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.dimension_reduction_results-a1.codimension_one_regularity-a1.simons_regular_cone-a1.hypercone_plane-a1.first_variation-a1`
- Child key: `smooth_to_c1`
- Declaration: `Submission.codim1_hcp_fv_smooth_to_C1_stationary`
- Exact Lean type: `∀ (P m : ℕ) (U M : Set (Euclid P)), IsOpen U → IsEmbeddedSubmanifold 1 m M → (∀ K : Set (Euclid P), IsCompact K → K ⊆ U → μHE[m] (M ∩ K) ≠ ∞) → (∀ Z : Euclid P → Euclid P, ContDiff ℝ (⊤ : ℕ∞) Z → HasCompactSupport Z → tsupport Z ⊆ U → ∫ x in M, LinearMap.trace ℝ (Euclid P) ((Submodule.span ℝ (tangentSpace M x)).starProjection.toLinearMap ∘ₗ (fderiv ℝ Z x).toLinearMap) ∂μHE[m] = 0) → ∀ X : Euclid P → Euclid P, ContDiff ℝ 1 X → HasCompactSupport X → tsupport X ⊆ U → ∫ x in M, LinearMap.trace ℝ (Euclid P) ((Submodule.span ℝ (tangentSpace M x)).starProjection.toLinearMap ∘ₗ (fderiv ℝ X x).toLinearMap) ∂μHE[m] = 0`

## Sibling prerequisites

- `root.dimension_reduction_results-a1.regular_point_density-a1.locally_closed-a1`
- `root.minimizing_implies_stationary-a1.diffeo_pushforward-a1.smooth_approximation-a1`
- `root.dimension_reduction_results-a1.codimension_one_regularity-a1.simons_regular_cone-a1.hypercone_plane-a1.first_variation-a1.tangent_projection-a1`
- `root.dimension_reduction_results-a1.codimension_one_regularity-a1.simons_regular_cone-a1.hypercone_plane-a1.first_variation-a1.trace_bound-a1`

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
