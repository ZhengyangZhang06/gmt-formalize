# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.compactness_of_minimizing_currents-a1.deformation_theorem-a1.cube_bv_median-a1.smooth_approx-a1.mollify_l1-a1.l1_contraction-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-compactness-of-minimizing-currents-a1-deformation-theorem-a1-cub-4c02ba4250/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.compactness_of_minimizing_currents-a1.deformation_theorem-a1.cube_bv_median-a1.smooth_approx-a1.mollify_l1-a1`
- Child key: `l1_contraction`
- Declaration: `Submission.cmcdt_cbm_sa_ml_l1_contraction`
- Exact Lean type: `∀ (n : ℕ) (k g : Euclid n → ℝ), (∀ z, 0 ≤ k z) → ∫ z, k z = 1 → AEStronglyMeasurable g volume → ∫⁻ x, ‖convolution k g (ContinuousLinearMap.lsmul ℝ ℝ) volume x‖ₑ ≤ ∫⁻ x, ‖g x‖ₑ`

## Sibling prerequisites

- None.

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
