# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.dimension_reduction_results-a1.codimension_one_regularity-a1.region_density_one-a1.local_unit_rep-a1.chart_perimeter-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-dimension-reduction-results-a1-codimension-one-regularity-a1-reg-1a867a3878/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.dimension_reduction_results-a1.codimension_one_regularity-a1.region_density_one-a1.local_unit_rep-a1`
- Child key: `chart_perimeter`
- Declaration: `Submission.codim1_lur_chart_locally_finite_perimeter`
- Exact Lean type: `∀ (P n : ℕ) (U N E : Set (Euclid P)) (ξN : Euclid P → MultiVector P (n + 1)) (T : GeometricCurrentOn U n) (x : Euclid P) (ι : Euclid (n + 1) →ₗᵢ[ℝ] Euclid P) (u : Euclid (n + 1) → Euclid P) (δ₁ δ₂ : ℝ), MeasurableSet E → E ⊆ N ∩ U → IsBoundaryOfRegion T E ξN → IsIntegerMultiplicity T → 0 < δ₁ → 0 < δ₂ → closedBall x (δ₁ + δ₂) ⊆ U → ContDiffOn ℝ 2 u (ball 0 δ₁) → (∀ v ∈ ball (0 : Euclid (n + 1)) δ₁, (∀ w : Euclid (n + 1), inner ℝ (ι w) (u v) = 0) ∧ ‖fderiv ℝ u v‖ ≤ 1 ∧ ‖u v‖ < δ₂ / 2 ∧ x + ι v + u v ∈ N ∧ ∀ α : Covector (Euclid P) (n + 1), ξN (x + ι v + u v) α * Real.sqrt (Matrix.det (Matrix.of fun i j : Fin (n + 1) => inner ℝ (ι (EuclideanSpace.single i 1) + fderiv ℝ u v (EuclideanSpace.single i 1)) (ι (EuclideanSpace.single j 1) + fderiv ℝ u v (EuclideanSpace.single j 1)))) = α (fun i => ι (EuclideanSpace.single i 1) + fderiv ℝ u v (EuclideanSpace.single i 1))) → (∀ (v : Euclid (n + 1)) (h : Euclid P), ‖v‖ < δ₁ → ‖h‖ < δ₂ → (∀ w : Euclid (n + 1), inner ℝ (ι w) h = 0) → x + ι v + h ∈ N → h = u v) → MeasurableSet (ball 0 δ₁ ∩ (fun y => x + ι y + u y) ⁻¹' E) ∧ ∀ K : Set (Euclid (n + 1)), IsCompact K → K ⊆ ball 0 δ₁ → ∃ C : ℝ, ∀ φ : Euclid (n + 1) → Euclid (n + 1), ContDiff ℝ (⊤ : ℕ∞) φ → HasCompactSupport φ → tsupport φ ⊆ K → (∀ y, ‖φ y‖ ≤ 1) → ∫ y in ball 0 δ₁ ∩ (fun y => x + ι y + u y) ⁻¹' E, LinearMap.trace ℝ (Euclid (n + 1)) (fderiv ℝ φ y : Euclid (n + 1) →ₗ[ℝ] Euclid (n + 1)) ≤ C`

## Sibling prerequisites

- `root.dimension_reduction_results-a1.codimension_one_regularity-a1.region_density_one-a1.local_unit_rep-a1.chart_divergence-a1`
- `root.density_one_implies_regular-a1.imrep_mass_and_support-a1.mass_upper_bound-a1`

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
