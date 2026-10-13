# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.dimension_reduction_results-a1.moving_blowups-a1.deformation_theorem-a1.cube_bv_median-a1.smooth_poincare-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-dimension-reduction-results-a1-moving-blowups-a1-deformation-the-9426bce89d/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.dimension_reduction_results-a1.moving_blowups-a1.deformation_theorem-a1.cube_bv_median-a1`
- Child key: `smooth_poincare`
- Declaration: `Submission.dimred_mbl_dt_cbm_smooth_poincare`
- Exact Lean type: `∀ (m : ℕ) (v : Euclid (m + 1) → ℝ) (δ : ℝ), ContDiff ℝ 1 v → 0 ≤ δ → ∫ x in {z : Euclid (m + 1) | ∀ i, δ < z i ∧ z i < 1 - δ}, ∫ y in {z : Euclid (m + 1) | ∀ i, δ < z i ∧ z i < 1 - δ}, |v x - v y| ≤ 2 ^ (m + 1) * Real.sqrt (m + 1) * ∫ x in {z : Euclid (m + 1) | ∀ i, δ < z i ∧ z i < 1 - δ}, ‖fderiv ℝ v x‖`

## Sibling prerequisites

- None.

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
