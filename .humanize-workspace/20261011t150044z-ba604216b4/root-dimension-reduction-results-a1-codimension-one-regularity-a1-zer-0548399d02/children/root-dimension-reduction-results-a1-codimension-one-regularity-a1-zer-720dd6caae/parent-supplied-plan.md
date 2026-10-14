# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.dimension_reduction_results-a1.codimension_one_regularity-a1.zero_scale_limit_plane-a1.bv_compactness-a1.mollify_field-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-dimension-reduction-results-a1-codimension-one-regularity-a1-zer-720dd6caae/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.dimension_reduction_results-a1.codimension_one_regularity-a1.zero_scale_limit_plane-a1.bv_compactness-a1`
- Child key: `mollify_field`
- Declaration: `Submission.codim1_zsl_pc_mollify_test_field`
- Exact Lean type: `∀ (m : ℕ) (F : Set (Euclid m)) (ρ : Euclid m → ℝ) (ψ : Euclid m → Euclid m) (r ε : ℝ), MeasurableSet F → ContDiff ℝ (⊤ : ℕ∞) ρ → (∀ z, 0 ≤ ρ z) → (∀ z, ε < ‖z‖ → ρ z = 0) → ∫ z, ρ z = 1 → ContDiff ℝ (⊤ : ℕ∞) ψ → HasCompactSupport ψ → tsupport ψ ⊆ ball (0 : Euclid m) r → (∀ v, ‖ψ v‖ ≤ 1) → ∃ ψ' : Euclid m → Euclid m, ContDiff ℝ (⊤ : ℕ∞) ψ' ∧ HasCompactSupport ψ' ∧ tsupport ψ' ⊆ ball (0 : Euclid m) (r + ε) ∧ (∀ v, ‖ψ' v‖ ≤ 1) ∧ ∫ v, (∫ z, ρ z * F.indicator (fun _ => (1 : ℝ)) (v - z)) * LinearMap.trace ℝ (Euclid m) (fderiv ℝ ψ v).toLinearMap = ∫ w in F, LinearMap.trace ℝ (Euclid m) (fderiv ℝ ψ' w).toLinearMap`

## Sibling prerequisites

- None.

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
