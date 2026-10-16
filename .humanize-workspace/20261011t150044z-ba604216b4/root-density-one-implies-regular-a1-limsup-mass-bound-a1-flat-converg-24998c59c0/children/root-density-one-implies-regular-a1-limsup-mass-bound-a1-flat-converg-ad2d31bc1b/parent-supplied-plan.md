# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.density_one_implies_regular-a1.limsup_mass_bound-a1.flat_convergence-a1.deformation-a1.cube_poincare-a1.smooth_duality-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-density-one-implies-regular-a1-limsup-mass-bound-a1-flat-converg-ad2d31bc1b/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.density_one_implies_regular-a1.limsup_mass_bound-a1.flat_convergence-a1.deformation-a1.cube_poincare-a1`
- Child key: `smooth_duality`
- Declaration: `Submission.dor_lmb_fcd_cp_smooth_duality`
- Exact Lean type: `∀ (P : ℕ) (w : Euclid P → ℝ) (W : Set (Euclid P)) (V : ℝ), IsOpen W → Bornology.IsBounded W → ContDiff ℝ (⊤ : ℕ∞) w → (∀ g : Euclid P → Euclid P, ContDiff ℝ (⊤ : ℕ∞) g → HasCompactSupport g → tsupport g ⊆ W → (∀ y, ‖g y‖ ≤ 1) → ∫ y, fderiv ℝ w y (g y) ≤ V) → ∫ y in W, ‖fderiv ℝ w y‖ ≤ V`

## Sibling prerequisites

- `root.regular_set_dense-a1.mass_eq_weight-a1.test_form_approx-a1.smooth_cutoff-a1`

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
