# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.dimension_reduction_results-a1.codimension_one_regularity-a1.simons_regular_cone-a1.area_comparison-a1.submanifold_area-a1.lintegral_image_of_local-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-dimension-reduction-results-a1-codimension-one-regularity-a1-sim-6e54c1b387/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.dimension_reduction_results-a1.codimension_one_regularity-a1.simons_regular_cone-a1.area_comparison-a1.submanifold_area-a1`
- Child key: `lintegral_image_of_local`
- Declaration: `Submission.codim1_ac_saf_lintegral_image_of_local`
- Exact Lean type: `∀ (P : ℕ) (μ : Measure (Euclid P)) (N : Set (Euclid P)) (Φ : Euclid P → Euclid P) (w : Euclid P → ℝ≥0∞), Continuous Φ → Injective Φ → (∀ y ∈ N, ∃ W : Set (Euclid P), IsOpen W ∧ y ∈ W ∧ ∀ B : Set (Euclid P), B ⊆ W ∩ N → MeasurableSet B → ∀ g : Euclid P → ℝ≥0∞, ∫⁻ z in Φ '' B, g z ∂μ = ∫⁻ x in B, w x * g (Φ x) ∂μ) → ∀ B : Set (Euclid P), B ⊆ N → MeasurableSet B → ∀ g : Euclid P → ℝ≥0∞, ∫⁻ z in Φ '' B, g z ∂μ = ∫⁻ x in B, w x * g (Φ x) ∂μ`

## Sibling prerequisites

- None.

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
