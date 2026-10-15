# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.density_one_implies_regular-a1.limsup_mass_bound-a1.flat_convergence-a1.deformation-a1.cube_poincare-a1.shrinking-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-density-one-implies-regular-a1-limsup-mass-bound-a1-flat-converg-539621c9cb/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.density_one_implies_regular-a1.limsup_mass_bound-a1.flat_convergence-a1.deformation-a1.cube_poincare-a1`
- Child key: `shrinking`
- Declaration: `Submission.dor_lmb_fcd_cp_shrinking`
- Exact Lean type: `∀ (m : ℕ) (f : Euclid (m + 1) → ℝ), IntegrableOn f {y : Euclid (m + 1) | ∀ i, 0 < y i ∧ y i < 1} → ∃ δ : ℝ, 0 < δ ∧ δ ≤ 1 / 4 ∧ volume {y : Euclid (m + 1) | ∀ i, δ < y i ∧ y i < 1 - δ} ≤ 1 ∧ volume ({y : Euclid (m + 1) | ∀ i, 0 < y i ∧ y i < 1} \ {y : Euclid (m + 1) | ∀ i, δ < y i ∧ y i < 1 - δ}) ≤ 1 / 4 ∧ ∫ y in {y : Euclid (m + 1) | ∀ i, 0 < y i ∧ y i < 1}, |f y| ≤ 2 * ∫ y in {y : Euclid (m + 1) | ∀ i, δ < y i ∧ y i < 1 - δ}, |f y|`

## Sibling prerequisites

- None.

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
