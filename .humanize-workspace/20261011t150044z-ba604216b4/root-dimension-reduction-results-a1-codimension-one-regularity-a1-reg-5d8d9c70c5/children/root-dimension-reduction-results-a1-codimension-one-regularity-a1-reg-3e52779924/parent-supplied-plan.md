# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.dimension_reduction_results-a1.codimension_one_regularity-a1.region_density_one-a1.local_unit_rep-a1.area_formula-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-dimension-reduction-results-a1-codimension-one-regularity-a1-reg-3e52779924/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.dimension_reduction_results-a1.codimension_one_regularity-a1.region_density_one-a1.local_unit_rep-a1`
- Child key: `area_formula`
- Declaration: `Submission.codim1_lur_rectifiable_area_formula`
- Exact Lean type: `∀ (m d P : ℕ) (D B : Set (Euclid d)) (G : Euclid d → Euclid P) (Q : Euclid d → Submodule ℝ (Euclid d)), 1 ≤ m → IsOpen D → ContDiffOn ℝ 1 G D → InjOn G D → (∀ v ∈ D, Injective (fderiv ℝ G v)) → MeasurableSet B → B ⊆ D → CountablyRectifiable m B → (∀ K : Set (Euclid d), IsCompact K → K ⊆ D → μHE[m] (B ∩ K) ≠ ∞) → (∀ᵐ v ∂(μHE[m].restrict B), HasApproximateTangentSpaceAt m B v (Q v)) → CountablyRectifiable m (G '' B) ∧ (∀ K : Set (Euclid d), IsCompact K → K ⊆ D → μHE[m] (G '' (B ∩ K)) ≠ ∞) ∧ ∃ J : Euclid d → ℝ, Measurable J ∧ (∀ v, 0 ≤ J v) ∧ (∀ᵐ v ∂(μHE[m].restrict B), ∀ σ : Fin m → Euclid d, Orthonormal ℝ σ → Submodule.span ℝ (Set.range σ) = Q v → J v = Real.sqrt (Matrix.det (Matrix.of fun i j : Fin m => inner ℝ (fderiv ℝ G v (σ i)) (fderiv ℝ G v (σ j))))) ∧ (∀ g : Euclid P → ℝ≥0∞, ∫⁻ w in G '' B, g w ∂μHE[m] = ∫⁻ v in B, ENNReal.ofReal (J v) * g (G v) ∂μHE[m]) ∧ ∀ f : Euclid P → ℝ, ∫ w in G '' B, f w ∂μHE[m] = ∫ v in B, J v * f (G v) ∂μHE[m]`

## Sibling prerequisites

- `root.minimizing_implies_stationary-a1.diffeo_pushforward-a1.bilipschitz_pieces-a1`
- `root.regular_components_are_minimizing-a1.approx_tangent_locality-a1`
- `root.minimizing_implies_stationary-a1.diffeo_pushforward-a1.piece_tangent_density-a1.piece_pullback-a1`
- `root.dimension_reduction_results-a1.codimension_one_regularity-a1.region_density_one-a1.local_unit_rep-a1.piece_tangent-a1`

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
