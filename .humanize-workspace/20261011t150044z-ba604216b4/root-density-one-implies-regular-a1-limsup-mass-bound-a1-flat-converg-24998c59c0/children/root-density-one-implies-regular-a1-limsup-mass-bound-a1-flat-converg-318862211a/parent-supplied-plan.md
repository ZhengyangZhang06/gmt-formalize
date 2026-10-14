# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.density_one_implies_regular-a1.limsup_mass_bound-a1.flat_convergence-a1.deformation-a1.cube_poincare-a1.mixed_point_identity-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-density-one-implies-regular-a1-limsup-mass-bound-a1-flat-converg-318862211a/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.density_one_implies_regular-a1.limsup_mass_bound-a1.flat_convergence-a1.deformation-a1.cube_poincare-a1`
- Child key: `mixed_point_identity`
- Declaration: `Submission.dor_lmb_fcd_cp_mixed_point_integral`
- Exact Lean type: `∀ (m : ℕ) (δ : ℝ) (k : Fin (m + 1)) (h : Euclid (m + 1) → ℝ), IntegrableOn h {y : Euclid (m + 1) | ∀ i, δ < y i ∧ y i < 1 - δ} → ∫ x in {y : Euclid (m + 1) | ∀ i, δ < y i ∧ y i < 1 - δ}, ∫ y in {y : Euclid (m + 1) | ∀ i, δ < y i ∧ y i < 1 - δ}, h (WithLp.toLp 2 (fun j => if j < k then y j else x j)) = (volume {y : Euclid (m + 1) | ∀ i, δ < y i ∧ y i < 1 - δ}).toReal * ∫ x in {y : Euclid (m + 1) | ∀ i, δ < y i ∧ y i < 1 - δ}, h x`

## Sibling prerequisites

- None.

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
