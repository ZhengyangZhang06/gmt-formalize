# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.dimension_reduction_results-a1.codimension_one_regularity-a1.region_density_one-a1.graph_chart-a1.orientation_along_graph-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-dimension-reduction-results-a1-codimension-one-regularity-a1-reg-ef5591c9af/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.dimension_reduction_results-a1.codimension_one_regularity-a1.region_density_one-a1.graph_chart-a1`
- Child key: `orientation_along_graph`
- Declaration: `Submission.codim1_rdo_gc_orientation_along_graph`
- Exact Lean type: `∀ (P n : ℕ) (N : Set (Euclid P)) (ξN : Euclid P → MultiVector P (n + 1)) (x : Euclid P) (ι : Euclid (n + 1) →ₗᵢ[ℝ] Euclid P) (u : Euclid (n + 1) → Euclid P) (δ : ℝ), IsOrientation (n + 1) N ξN → (∀ α : Covector (Euclid P) (n + 1), ξN x α = α (fun i => ι (EuclideanSpace.single i 1))) → 0 < δ → u 0 = 0 → fderiv ℝ u 0 = 0 → ContDiffOn ℝ 1 u (ball 0 δ) → (∀ v ∈ ball (0 : Euclid (n + 1)) δ, ∀ w : Euclid (n + 1), inner ℝ (ι w) (u v) = 0) → (∀ v ∈ ball (0 : Euclid (n + 1)) δ, x + ι v + u v ∈ N) → ∀ v ∈ ball (0 : Euclid (n + 1)) δ, ∀ α : Covector (Euclid P) (n + 1), ξN (x + ι v + u v) α * Real.sqrt (Matrix.det (Matrix.of fun i j : Fin (n + 1) => inner ℝ (ι (EuclideanSpace.single i 1) + fderiv ℝ u v (EuclideanSpace.single i 1)) (ι (EuclideanSpace.single j 1) + fderiv ℝ u v (EuclideanSpace.single j 1)))) = α (fun i => ι (EuclideanSpace.single i 1) + fderiv ℝ u v (EuclideanSpace.single i 1))`

## Sibling prerequisites

- `root.dimension_reduction_results-a1.codimension_one_regularity-a1.region_density_one-a1.graph_chart-a1.gram_unit_orientation-a1`
- `root.regular_set_dense-a1.integer_combination-a1.orientation_sign-a1`
- `root.density_one_implies_regular-a1.imrep_mass_and_support-a1.unit_orientation_duality-a1`
- `root.density_one_implies_regular-a1.mean_curvature_monotonicity-a1.chart_tangent_space-a1.range_subset_tangent-a1`
- `root.density_one_implies_regular-a1.epsilon_regularity-a1.graph_cycle_regular-a1.graph_orientation_jacobian-a1.continuous_covector_eval-a1`

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
