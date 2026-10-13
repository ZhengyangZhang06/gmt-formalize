# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.dimension_reduction_results-a1.codimension_one_regularity-a1.region_density_one-a1.graph_chart-a1.graph_over_tangent-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-dimension-reduction-results-a1-codimension-one-regularity-a1-reg-e764c97118/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.dimension_reduction_results-a1.codimension_one_regularity-a1.region_density_one-a1.graph_chart-a1`
- Child key: `graph_over_tangent`
- Declaration: `Submission.codim1_rdo_gc_graph_over_tangent`
- Exact Lean type: `∀ (P d : ℕ) (U N : Set (Euclid P)) (x : Euclid P) (ι : Euclid d →ₗᵢ[ℝ] Euclid P), IsOpen U → IsEmbeddedSubmanifold 2 d N → x ∈ N ∩ U → Set.range ι = tangentSpace N x → ∃ (u : Euclid d → Euclid P) (δ₁ δ₂ : ℝ), 0 < δ₁ ∧ 0 < δ₂ ∧ closedBall x (δ₁ + δ₂) ⊆ U ∧ u 0 = 0 ∧ fderiv ℝ u 0 = 0 ∧ ContDiffOn ℝ 2 u (ball 0 δ₁) ∧ (∀ v ∈ ball (0 : Euclid d) δ₁, (∀ w : Euclid d, inner ℝ (ι w) (u v) = 0) ∧ ‖fderiv ℝ u v‖ ≤ 1 ∧ ‖u v‖ < δ₂ / 2 ∧ x + ι v + u v ∈ N) ∧ ∀ (v : Euclid d) (h : Euclid P), ‖v‖ < δ₁ → ‖h‖ < δ₂ → (∀ w : Euclid d, inner ℝ (ι w) h = 0) → x + ι v + h ∈ N → h = u v`

## Sibling prerequisites

- `root.dimension_reduction_results-a1.codimension_one_regularity-a1.region_density_one-a1.graph_chart-a1.local_inverse_c2-a1`
- `root.density_one_implies_regular-a1.mean_curvature_monotonicity-a1.chart_tangent_space-a1`

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
