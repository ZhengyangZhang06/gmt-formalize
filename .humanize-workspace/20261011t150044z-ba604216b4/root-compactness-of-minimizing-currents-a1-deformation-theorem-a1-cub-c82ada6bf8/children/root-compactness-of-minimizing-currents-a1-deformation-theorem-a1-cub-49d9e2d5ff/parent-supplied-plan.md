# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.compactness_of_minimizing_currents-a1.deformation_theorem-a1.cube_bv_median-a1.bv_poincare-a1.osc_exhaustion-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-compactness-of-minimizing-currents-a1-deformation-theorem-a1-cub-49d9e2d5ff/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.compactness_of_minimizing_currents-a1.deformation_theorem-a1.cube_bv_median-a1.bv_poincare-a1`
- Child key: `osc_exhaustion`
- Declaration: `Submission.cmcdt_cbm_bvp_osc_le_of_inner_cubes`
- Exact Lean type: `∀ (m : ℕ) (u : Euclid (m + 1) → ℝ) (K : ℝ), IntegrableOn u {y : Euclid (m + 1) | ∀ i, 0 < y i ∧ y i < 1} → (∀ δ : ℝ, 0 < δ → δ < 1 / 2 → ∫ x in {z : Euclid (m + 1) | ∀ i, δ < z i ∧ z i < 1 - δ}, ∫ y in {z : Euclid (m + 1) | ∀ i, δ < z i ∧ z i < 1 - δ}, |u x - u y| ≤ K) → ∫ x in {y : Euclid (m + 1) | ∀ i, 0 < y i ∧ y i < 1}, ∫ y in {y : Euclid (m + 1) | ∀ i, 0 < y i ∧ y i < 1}, |u x - u y| ≤ K`

## Sibling prerequisites

- `root.compactness_of_minimizing_currents-a1.deformation_theorem-a1.cube_bv_median-a1.bv_poincare-a1.unit_cube_volume-a1`

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
