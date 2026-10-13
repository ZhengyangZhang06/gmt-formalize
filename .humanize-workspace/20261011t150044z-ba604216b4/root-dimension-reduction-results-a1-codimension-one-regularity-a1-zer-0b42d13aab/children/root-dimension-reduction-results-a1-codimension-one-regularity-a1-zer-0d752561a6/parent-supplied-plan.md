# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.dimension_reduction_results-a1.codimension_one_regularity-a1.zero_scale_limit_plane-a1.graph_blowup_limit-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-dimension-reduction-results-a1-codimension-one-regularity-a1-zer-0d752561a6/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.dimension_reduction_results-a1.codimension_one_regularity-a1.zero_scale_limit_plane-a1`
- Child key: `graph_blowup_limit`
- Declaration: `Submission.codim1_zsl_graph_blowup_limit`
- Exact Lean type: `∀ (n k : ℕ) (U N E : Set (Euclid (n + 1 + k))) (ξN : Euclid (n + 1 + k) → MultiVector (n + 1 + k) (n + 1)) (T : GeometricCurrentOn U n) (x : Euclid (n + 1 + k)) (xs : ℕ → Euclid (n + 1 + k)) (lams : ℕ → ℝ) (hlams : ∀ i, 0 < lams i) (S : GeometricCurrentOn (univ : Set (Euclid (n + 1 + k))) n) (ι : Euclid (n + 1) →ₗᵢ[ℝ] Euclid (n + 1 + k)) (ι' : Euclid k →ₗᵢ[ℝ] Euclid (n + 1 + k)) (u : Euclid (n + 1) → Euclid k) (δ₁ δ₂ C₀ : ℝ), IsOpen U → MeasurableSet E → E ⊆ N → IsBoundaryOfRegion T E ξN → x ∈ U → Tendsto xs atTop (𝓝 x) → Tendsto lams atTop (𝓝 0) → (∃ C r₀ : ℝ, 0 < r₀ ∧ ∀ y ∈ ball x r₀, ∀ ρ : ℝ, 0 < ρ → ρ < r₀ → T.massOn (ball y ρ) ≤ ENNReal.ofReal (C * ρ ^ n)) → ConvergesWeakly (fun i => blowUp T (xs i) (lams i) (hlams i).ne') S → (∀ i, ∃ p ∈ N, dist p (xs i) ≤ C₀ * lams i) → (∀ v w, inner ℝ (ι v) (ι' w) = 0) → (∀ y : Euclid (n + 1 + k), ∃ v w, y = ι v + ι' w) → 0 < δ₁ → 0 < δ₂ → ContDiffOn ℝ 1 u (ball 0 δ₁) → u 0 = 0 → fderiv ℝ u 0 = 0 → (∀ v ∈ ball (0 : Euclid (n + 1)) δ₁, u v ∈ ball (0 : Euclid k) δ₂) → N ∩ {y | ∃ v ∈ ball (0 : Euclid (n + 1)) δ₁, ∃ w ∈ ball (0 : Euclid k) δ₂, y = x + ι v + ι' w} = (fun v => x + ι v + ι' (u v)) '' ball (0 : Euclid (n + 1)) δ₁ → (∀ α : Covector (Euclid (n + 1 + k)) (n + 1), ξN x α = α (fun j => ι (EuclideanSpace.single j (1 : ℝ)))) → (∀ v ∈ ball (0 : Euclid (n + 1)) δ₁, ∀ α : Covector (Euclid (n + 1 + k)) (n + 1), α (fun j => fderiv ℝ (fun v => x + ι v + ι' (u v)) v (EuclideanSpace.single j (1 : ℝ))) = Real.sqrt (((fderiv ℝ (fun v => x + ι v + ι' (u v)) v).adjoint ∘L fderiv ℝ (fun v => x + ι v + ι' (u v)) v).det) * ξN (x + ι v + ι' (u v)) α) → ∃ (b : Euclid k) (F : Set (Euclid (n + 1 + k))), MeasurableSet F ∧ F ⊆ {y | ∃ w, y = ι w + ι' b} ∧ IsBoundaryOfRegion S F (fun _ => ξN x)`

## Sibling prerequisites

- `root.dimension_reduction_results-a1.codimension_one_regularity-a1.zero_scale_limit_plane-a1.blowup_region-a1`
- `root.dimension_reduction_results-a1.codimension_one_regularity-a1.zero_scale_limit_plane-a1.graph_area-a1`
- `root.dimension_reduction_results-a1.codimension_one_regularity-a1.zero_scale_limit_plane-a1.flat_limit-a1`
- `root.density_and_tangent_cones-a1.blowup_scaling-a1.testform_correspondence-a1`

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
