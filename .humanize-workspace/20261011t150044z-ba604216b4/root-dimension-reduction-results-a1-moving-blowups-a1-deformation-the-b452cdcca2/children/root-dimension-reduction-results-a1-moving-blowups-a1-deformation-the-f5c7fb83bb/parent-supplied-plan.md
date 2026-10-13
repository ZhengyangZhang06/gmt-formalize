# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.dimension_reduction_results-a1.moving_blowups-a1.deformation_theorem-a1.cube_bv_median-a1.bv_poincare-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-dimension-reduction-results-a1-moving-blowups-a1-deformation-the-f5c7fb83bb/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.dimension_reduction_results-a1.moving_blowups-a1.deformation_theorem-a1.cube_bv_median-a1`
- Child key: `bv_poincare`
- Declaration: `Submission.dimred_mbl_dt_cbm_bv_poincare`
- Exact Lean type: `∀ (m : ℕ) (u : Euclid (m + 1) → ℝ) (V : ℝ), IntegrableOn u {y : Euclid (m + 1) | ∀ i, 0 < y i ∧ y i < 1} → (∀ g : Euclid (m + 1) → Euclid (m + 1), ContDiff ℝ (⊤ : ℕ∞) g → HasCompactSupport g → tsupport g ⊆ {y : Euclid (m + 1) | ∀ i, 0 < y i ∧ y i < 1} → (∀ y, ‖g y‖ ≤ 1) → ∫ y in {y : Euclid (m + 1) | ∀ i, 0 < y i ∧ y i < 1}, u y * LinearMap.trace ℝ (Euclid (m + 1)) (fderiv ℝ g y) ≤ V) → ∃ c : ℝ, ∫ y in {y : Euclid (m + 1) | ∀ i, 0 < y i ∧ y i < 1}, |u y - c| ≤ 2 ^ (m + 2) * Real.sqrt (m + 1) * V`

## Sibling prerequisites

- `root.dimension_reduction_results-a1.moving_blowups-a1.deformation_theorem-a1.cube_bv_median-a1.smooth_approx-a1`
- `root.dimension_reduction_results-a1.moving_blowups-a1.deformation_theorem-a1.cube_bv_median-a1.smooth_poincare-a1`

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
