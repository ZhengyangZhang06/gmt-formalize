# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.dimension_reduction_results-a1.codimension_one_regularity-a1.zero_scale_limit_plane-a1.bv_compactness-a1.mollified_gradient-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-dimension-reduction-results-a1-codimension-one-regularity-a1-zer-b178d0320c/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.dimension_reduction_results-a1.codimension_one_regularity-a1.zero_scale_limit_plane-a1.bv_compactness-a1`
- Child key: `mollified_gradient`
- Declaration: `Submission.codim1_zsl_pc_mollify_grad_bound`
- Exact Lean type: `∀ (m : ℕ) (F : Set (Euclid m)) (ρ : Euclid m → ℝ) (r ε c : ℝ), MeasurableSet F → ContDiff ℝ (⊤ : ℕ∞) ρ → (∀ z, 0 ≤ ρ z) → (∀ z, ε < ‖z‖ → ρ z = 0) → ∫ z, ρ z = 1 → (∀ φ : Euclid m → Euclid m, ContDiff ℝ (⊤ : ℕ∞) φ → HasCompactSupport φ → tsupport φ ⊆ ball (0 : Euclid m) (r + ε) → (∀ v, ‖φ v‖ ≤ 1) → ∫ v in F, LinearMap.trace ℝ (Euclid m) (fderiv ℝ φ v).toLinearMap ≤ c) → ContDiff ℝ (⊤ : ℕ∞) (fun v => ∫ z, ρ z * F.indicator (fun _ => (1 : ℝ)) (v - z)) ∧ ∫⁻ v in ball (0 : Euclid m) r, ‖fderiv ℝ (fun v => ∫ z, ρ z * F.indicator (fun _ => (1 : ℝ)) (v - z)) v‖ₑ ≤ ENNReal.ofReal c`

## Sibling prerequisites

- `root.dimension_reduction_results-a1.codimension_one_regularity-a1.zero_scale_limit_plane-a1.bv_compactness-a1.smooth_variation-a1`
- `root.dimension_reduction_results-a1.codimension_one_regularity-a1.zero_scale_limit_plane-a1.bv_compactness-a1.mollify_field-a1`

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
