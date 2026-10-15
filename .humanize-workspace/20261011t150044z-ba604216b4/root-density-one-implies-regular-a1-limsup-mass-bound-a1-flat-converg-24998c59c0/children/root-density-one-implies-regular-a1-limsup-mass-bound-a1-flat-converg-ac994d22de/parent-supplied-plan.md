# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.density_one_implies_regular-a1.limsup_mass_bound-a1.flat_convergence-a1.deformation-a1.cube_poincare-a1.smooth_poincare-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-density-one-implies-regular-a1-limsup-mass-bound-a1-flat-converg-ac994d22de/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.density_one_implies_regular-a1.limsup_mass_bound-a1.flat_convergence-a1.deformation-a1.cube_poincare-a1`
- Child key: `smooth_poincare`
- Declaration: `Submission.dor_lmb_fcd_cp_smooth_poincare`
- Exact Lean type: `∀ (m : ℕ) (v : Euclid (m + 1) → ℝ) (δ : ℝ), ContDiff ℝ 1 v → 0 ≤ δ → δ < 1 / 2 → ∫ x in {y : Euclid (m + 1) | ∀ i, δ < y i ∧ y i < 1 - δ}, ∫ y in {y : Euclid (m + 1) | ∀ i, δ < y i ∧ y i < 1 - δ}, |v x - v y| ≤ ((m : ℝ) + 1) * (1 - 2 * δ) * (volume {y : Euclid (m + 1) | ∀ i, δ < y i ∧ y i < 1 - δ}).toReal * ∫ x in {y : Euclid (m + 1) | ∀ i, δ < y i ∧ y i < 1 - δ}, ‖fderiv ℝ v x‖`

## Sibling prerequisites

- `root.density_one_implies_regular-a1.limsup_mass_bound-a1.flat_convergence-a1.deformation-a1.cube_poincare-a1.coordinate_step-a1`

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
