# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.dimension_reduction_results-a1.codimension_one_regularity-a1.region_density_one-a1.local_unit_rep-a1.chart_divergence-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-dimension-reduction-results-a1-codimension-one-regularity-a1-reg-a3c73c9e47/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.dimension_reduction_results-a1.codimension_one_regularity-a1.region_density_one-a1.local_unit_rep-a1`
- Child key: `chart_divergence`
- Declaration: `Submission.codim1_lur_chart_divergence_formula`
- Exact Lean type: `∀ (P n : ℕ) (U N E : Set (Euclid P)) (ξN : Euclid P → MultiVector P (n + 1)) (T : GeometricCurrentOn U n) (x : Euclid P) (ι : Euclid (n + 1) →ₗᵢ[ℝ] Euclid P) (u : Euclid (n + 1) → Euclid P) (δ₁ δ₂ : ℝ), MeasurableSet E → E ⊆ N ∩ U → IsBoundaryOfRegion T E ξN → 0 < δ₁ → 0 < δ₂ → ContDiffOn ℝ 2 u (ball 0 δ₁) → (∀ v ∈ ball (0 : Euclid (n + 1)) δ₁, (∀ w : Euclid (n + 1), inner ℝ (ι w) (u v) = 0) ∧ ‖fderiv ℝ u v‖ ≤ 1 ∧ ‖u v‖ < δ₂ / 2 ∧ x + ι v + u v ∈ N ∧ ∀ α : Covector (Euclid P) (n + 1), ξN (x + ι v + u v) α * Real.sqrt (Matrix.det (Matrix.of fun i j : Fin (n + 1) => inner ℝ (ι (EuclideanSpace.single i 1) + fderiv ℝ u v (EuclideanSpace.single i 1)) (ι (EuclideanSpace.single j 1) + fderiv ℝ u v (EuclideanSpace.single j 1)))) = α (fun i => ι (EuclideanSpace.single i 1) + fderiv ℝ u v (EuclideanSpace.single i 1))) → (∀ (v : Euclid (n + 1)) (h : Euclid P), ‖v‖ < δ₁ → ‖h‖ < δ₂ → (∀ w : Euclid (n + 1), inner ℝ (ι w) h = 0) → x + ι v + h ∈ N → h = u v) → ∀ (ω : TestFormOn U n) (Φ : Euclid (n + 1) → Euclid (n + 1)), tsupport (ω : DifferentialForm (Euclid P) n) ⊆ {w : Euclid P | ‖ContinuousLinearMap.adjoint ι.toContinuousLinearMap (w - x)‖ < δ₁ ∧ ‖w - x - ι (ContinuousLinearMap.adjoint ι.toContinuousLinearMap (w - x))‖ < δ₂} → Φ = (ball (0 : Euclid (n + 1)) δ₁).indicator (fun v => ∑ j : Fin (n + 1), ((-1 : ℝ) ^ (j : ℕ) * (ω : DifferentialForm (Euclid P) n) (x + ι v + u v) (fun k => fderiv ℝ (fun y => x + ι y + u y) v (EuclideanSpace.single (j.succAbove k) 1))) • EuclideanSpace.single j (1 : ℝ)) → ContDiff ℝ 1 Φ ∧ HasCompactSupport Φ ∧ tsupport Φ ⊆ ball 0 δ₁ ∧ T ω = ∫ v in ball 0 δ₁ ∩ (fun y => x + ι y + u y) ⁻¹' E, LinearMap.trace ℝ (Euclid (n + 1)) (fderiv ℝ Φ v : Euclid (n + 1) →ₗ[ℝ] Euclid (n + 1))`

## Sibling prerequisites

- None.

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
