# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.dimension_reduction_results-a1.codimension_one_regularity-a1.zero_scale_limit_plane-a1.graph_chart-a1.local_graph-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-dimension-reduction-results-a1-codimension-one-regularity-a1-zer-0083dd2726/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.dimension_reduction_results-a1.codimension_one_regularity-a1.zero_scale_limit_plane-a1.graph_chart-a1`
- Child key: `local_graph`
- Declaration: `Submission.codim1_zsl_gc_local_graph`
- Exact Lean type: `∀ (d k : ℕ) (N : Set (Euclid (d + k))) (x : Euclid (d + k)) (ι : Euclid d →ₗᵢ[ℝ] Euclid (d + k)) (ι' : Euclid k →ₗᵢ[ℝ] Euclid (d + k)), IsEmbeddedSubmanifold 2 d N → x ∈ N → (∀ v w, inner ℝ (ι v) (ι' w) = 0) → (∀ y : Euclid (d + k), ∃ v w, y = ι v + ι' w) → tangentSpace N x ⊆ Set.range ι → ∃ (O : Set (Euclid d)) (u : Euclid d → Euclid k) (s : ℝ), IsOpen O ∧ (0 : Euclid d) ∈ O ∧ 0 < s ∧ ContDiffOn ℝ 1 u O ∧ u 0 = 0 ∧ fderiv ℝ u 0 = 0 ∧ (∀ v ∈ O, x + ι v + ι' (u v) ∈ N) ∧ ∀ y ∈ N, dist y x < s → ∃ v ∈ O, y = x + ι v + ι' (u v)`

## Sibling prerequisites

- `root.dimension_reduction_results-a1.codimension_one_regularity-a1.zero_scale_limit_plane-a1.graph_chart-a1.local_inverse-a1`
- `root.density_one_implies_regular-a1.mean_curvature_monotonicity-a1.chart_tangent_space-a1.range_subset_tangent-a1`
- `root.density_one_implies_regular-a1.mean_curvature_monotonicity-a1.chart_tangent_space-a1.inverse_continuity-a1`

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
