# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.dimension_reduction_results-a1.codimension_one_regularity-a1.zero_scale_limit_plane-a1.bv_compactness-a1.translation_estimate-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-dimension-reduction-results-a1-codimension-one-regularity-a1-zer-1eb79729b7/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.dimension_reduction_results-a1.codimension_one_regularity-a1.zero_scale_limit_plane-a1.bv_compactness-a1`
- Child key: `translation_estimate`
- Declaration: `Submission.codim1_zsl_pc_translation_estimate`
- Exact Lean type: `∀ (m : ℕ) (F : Set (Euclid m)) (R c : ℝ), MeasurableSet F → (∀ φ : Euclid m → Euclid m, ContDiff ℝ (⊤ : ℕ∞) φ → HasCompactSupport φ → tsupport φ ⊆ ball (0 : Euclid m) (R + 2) → (∀ v, ‖φ v‖ ≤ 1) → ∫ v in F, LinearMap.trace ℝ (Euclid m) (fderiv ℝ φ v).toLinearMap ≤ c) → ∀ h : Euclid m, ‖h‖ ≤ 1 → volume (symmDiff ((fun v => v + h) ⁻¹' F) F ∩ ball (0 : Euclid m) R) ≤ ENNReal.ofReal (c * ‖h‖)`

## Sibling prerequisites

- `root.dimension_reduction_results-a1.codimension_one_regularity-a1.zero_scale_limit_plane-a1.bv_compactness-a1.mollify_l1-a1`
- `root.dimension_reduction_results-a1.codimension_one_regularity-a1.zero_scale_limit_plane-a1.bv_compactness-a1.smooth_translate-a1`
- `root.dimension_reduction_results-a1.codimension_one_regularity-a1.zero_scale_limit_plane-a1.bv_compactness-a1.mollified_gradient-a1`

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
