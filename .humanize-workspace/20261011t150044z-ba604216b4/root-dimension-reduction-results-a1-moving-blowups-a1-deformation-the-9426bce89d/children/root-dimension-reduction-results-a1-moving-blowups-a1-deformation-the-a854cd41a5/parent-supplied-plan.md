# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.dimension_reduction_results-a1.moving_blowups-a1.deformation_theorem-a1.cube_bv_median-a1.smooth_poincare-a1.convex_slice_bound-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-dimension-reduction-results-a1-moving-blowups-a1-deformation-the-a854cd41a5/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.dimension_reduction_results-a1.moving_blowups-a1.deformation_theorem-a1.cube_bv_median-a1.smooth_poincare-a1`
- Child key: `convex_slice_bound`
- Declaration: `Submission.dimred_mbl_dt_cbm_sp_convex_slice_bound`
- Exact Lean type: `∀ (n : ℕ) (Q : Set (Euclid n)) (g : Euclid n → ℝ≥0∞), Convex ℝ Q → MeasurableSet Q → Measurable g → ∀ t ∈ Icc (0 : ℝ) 1, ∫⁻ x in Q, ∫⁻ y in Q, g ((1 - t) • y + t • x) ≤ 2 ^ n * volume Q * ∫⁻ z in Q, g z`

## Sibling prerequisites

- None.

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
