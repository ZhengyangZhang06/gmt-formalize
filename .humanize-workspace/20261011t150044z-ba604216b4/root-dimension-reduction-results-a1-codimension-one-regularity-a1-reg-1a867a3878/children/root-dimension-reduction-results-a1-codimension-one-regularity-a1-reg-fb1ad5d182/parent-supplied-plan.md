# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.dimension_reduction_results-a1.codimension_one_regularity-a1.region_density_one-a1.local_unit_rep-a1.chart_perimeter-a1.test_form-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-dimension-reduction-results-a1-codimension-one-regularity-a1-reg-fb1ad5d182/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.dimension_reduction_results-a1.codimension_one_regularity-a1.region_density_one-a1.local_unit_rep-a1.chart_perimeter-a1`
- Child key: `test_form`
- Declaration: `Submission.codim1_lur_chart_test_form_exists`
- Exact Lean type: `∀ (P n : ℕ) (U : Set (Euclid P)) (x : Euclid P) (ι : Euclid (n + 1) →ₗᵢ[ℝ] Euclid P) (u : Euclid (n + 1) → Euclid P) (δ₁ δ₂ : ℝ) (φ : Euclid (n + 1) → Euclid (n + 1)), 0 < δ₂ → closedBall x (δ₁ + δ₂) ⊆ U → DifferentiableOn ℝ u (ball 0 δ₁) → (∀ v ∈ ball (0 : Euclid (n + 1)) δ₁, ∀ w : Euclid (n + 1), inner ℝ (ι w) (u v) = 0) → (∀ v ∈ ball (0 : Euclid (n + 1)) δ₁, ‖u v‖ < δ₂ / 2) → ContDiff ℝ (⊤ : ℕ∞) φ → HasCompactSupport φ → tsupport φ ⊆ ball 0 δ₁ → (∀ y, ‖φ y‖ ≤ 1) → ∃ ω : TestFormOn U n, tsupport (ω : DifferentialForm (Euclid P) n) ⊆ {w : Euclid P | ‖ContinuousLinearMap.adjoint ι.toContinuousLinearMap (w - x)‖ < δ₁ ∧ ‖w - x - ι (ContinuousLinearMap.adjoint ι.toContinuousLinearMap (w - x))‖ < δ₂} ∧ tsupport (ω : DifferentialForm (Euclid P) n) ⊆ closedBall x (δ₁ + δ₂) ∧ (∀ w, covectorEuclideanNorm ((ω : DifferentialForm (Euclid P) n) w) ≤ ((n + 1).factorial : ℝ) * Real.sqrt ((P : ℝ) ^ n)) ∧ φ = (ball (0 : Euclid (n + 1)) δ₁).indicator (fun v => ∑ j : Fin (n + 1), ((-1 : ℝ) ^ (j : ℕ) * (ω : DifferentialForm (Euclid P) n) (x + ι v + u v) (fun k => fderiv ℝ (fun y => x + ι y + u y) v (EuclideanSpace.single (j.succAbove k) 1))) • EuclideanSpace.single j (1 : ℝ))`

## Sibling prerequisites

- `root.dimension_reduction_results-a1.codimension_one_regularity-a1.region_density_one-a1.local_unit_rep-a1.chart_perimeter-a1.chart_geometry-a1`
- `root.dimension_reduction_results-a1.codimension_one_regularity-a1.region_density_one-a1.local_unit_rep-a1.chart_perimeter-a1.det_covector-a1`
- `root.dimension_reduction_results-a1.codimension_one_regularity-a1.region_density_one-a1.local_unit_rep-a1.chart_perimeter-a1.coeff_bound-a1`
- `root.dimension_reduction_results-a1.codimension_one_regularity-a1.region_density_one-a1.local_unit_rep-a1.chart_perimeter-a1.det_laplace-a1`

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
