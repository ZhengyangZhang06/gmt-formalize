# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.dimension_reduction_results-a1.codimension_one_regularity-a1.region_density_one-a1.local_unit_rep-a1.chart_perimeter-a1.chart_geometry-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-dimension-reduction-results-a1-codimension-one-regularity-a1-reg-a08e0327a7/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.dimension_reduction_results-a1.codimension_one_regularity-a1.region_density_one-a1.local_unit_rep-a1.chart_perimeter-a1`
- Child key: `chart_geometry`
- Declaration: `Submission.codim1_lur_graph_chart_adjoint_identities`
- Exact Lean type: `∀ (P n : ℕ) (x : Euclid P) (ι : Euclid (n + 1) →ₗᵢ[ℝ] Euclid P) (u : Euclid (n + 1) → Euclid P) (δ₁ : ℝ), DifferentiableOn ℝ u (ball 0 δ₁) → (∀ v ∈ ball (0 : Euclid (n + 1)) δ₁, ∀ w : Euclid (n + 1), inner ℝ (ι w) (u v) = 0) → ‖ContinuousLinearMap.adjoint ι.toContinuousLinearMap‖ ≤ 1 ∧ (∀ z : Euclid (n + 1), ContinuousLinearMap.adjoint ι.toContinuousLinearMap (ι z) = z) ∧ ∀ v ∈ ball (0 : Euclid (n + 1)) δ₁, ContinuousLinearMap.adjoint ι.toContinuousLinearMap (x + ι v + u v - x) = v ∧ x + ι v + u v - x - ι (ContinuousLinearMap.adjoint ι.toContinuousLinearMap (x + ι v + u v - x)) = u v ∧ ∀ y : Euclid (n + 1), ContinuousLinearMap.adjoint ι.toContinuousLinearMap (fderiv ℝ (fun y => x + ι y + u y) v y) = y`

## Sibling prerequisites

- None.

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
