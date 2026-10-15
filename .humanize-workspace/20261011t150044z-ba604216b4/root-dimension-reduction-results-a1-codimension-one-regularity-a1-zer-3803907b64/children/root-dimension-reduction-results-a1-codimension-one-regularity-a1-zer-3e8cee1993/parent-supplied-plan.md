# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.dimension_reduction_results-a1.codimension_one_regularity-a1.zero_scale_limit_plane-a1.graph_chart-a1.orientation_along_graph-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-dimension-reduction-results-a1-codimension-one-regularity-a1-zer-3e8cee1993/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.dimension_reduction_results-a1.codimension_one_regularity-a1.zero_scale_limit_plane-a1.graph_chart-a1`
- Child key: `orientation_along_graph`
- Declaration: `Submission.codim1_zsl_gc_orientation_along_graph`
- Exact Lean type: `∀ (n k : ℕ) (N : Set (Euclid (n + 1 + k))) (ξN : Euclid (n + 1 + k) → MultiVector (n + 1 + k) (n + 1)) (x : Euclid (n + 1 + k)) (ι : Euclid (n + 1) →ₗᵢ[ℝ] Euclid (n + 1 + k)) (ι' : Euclid k →ₗᵢ[ℝ] Euclid (n + 1 + k)) (u : Euclid (n + 1) → Euclid k) (δ : ℝ), IsOrientation (n + 1) N ξN → (∀ v w, inner ℝ (ι v) (ι' w) = 0) → 0 < δ → ContDiffOn ℝ 1 u (ball 0 δ) → u 0 = 0 → fderiv ℝ u 0 = 0 → (∀ v ∈ ball (0 : Euclid (n + 1)) δ, x + ι v + ι' (u v) ∈ N) → (∀ α : Covector (Euclid (n + 1 + k)) (n + 1), ξN x α = α (fun j => ι (EuclideanSpace.single j (1 : ℝ)))) → ∀ v ∈ ball (0 : Euclid (n + 1)) δ, ∀ α : Covector (Euclid (n + 1 + k)) (n + 1), α (fun j => fderiv ℝ (fun v => x + ι v + ι' (u v)) v (EuclideanSpace.single j (1 : ℝ))) = Real.sqrt (((fderiv ℝ (fun v => x + ι v + ι' (u v)) v).adjoint ∘L fderiv ℝ (fun v => x + ι v + ι' (u v)) v).det) * ξN (x + ι v + ι' (u v)) α`

## Sibling prerequisites

- `root.density_one_implies_regular-a1.epsilon_regularity-a1.graph_cycle_regular-a1.graph_orientation_jacobian-a1`
- `root.regular_set_dense-a1.integer_combination-a1.orientation_sign-a1`
- `root.density_one_implies_regular-a1.mean_curvature_monotonicity-a1.chart_tangent_space-a1.range_subset_tangent-a1`

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
