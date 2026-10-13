# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.dimension_reduction_results-a1.codimension_one_regularity-a1.region_density_one-a1.local_unit_rep-a1.area_formula-a1.bochner_transfer-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-dimension-reduction-results-a1-codimension-one-regularity-a1-reg-0d4f6dc6e0/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.dimension_reduction_results-a1.codimension_one_regularity-a1.region_density_one-a1.local_unit_rep-a1.area_formula-a1`
- Child key: `bochner_transfer`
- Declaration: `Submission.codim1_lura_integral_image_of_lintegral`
- Exact Lean type: `∀ (d P : ℕ) (μ : Measure (Euclid P)) (ν : Measure (Euclid d)) (B : Set (Euclid d)) (G : Euclid d → Euclid P) (J : Euclid d → ℝ), MeasurableSet B → ContinuousOn G B → InjOn G B → Measurable J → (∀ v, 0 ≤ J v) → (∀ g : Euclid P → ℝ≥0∞, ∫⁻ w in G '' B, g w ∂μ = ∫⁻ v in B, ENNReal.ofReal (J v) * g (G v) ∂ν) → ∀ f : Euclid P → ℝ, ∫ w in G '' B, f w ∂μ = ∫ v in B, J v * f (G v) ∂ν`

## Sibling prerequisites

- None.

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
