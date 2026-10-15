# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.density_one_implies_regular-a1.limsup_mass_bound-a1.projected_comparison-a1.competitor_mass-a1.vd_add-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-density-one-implies-regular-a1-limsup-mass-bound-a1-projected-co-af45c0d81e/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.density_one_implies_regular-a1.limsup_mass_bound-a1.projected_comparison-a1.competitor_mass-a1`
- Child key: `vd_add`
- Declaration: `Submission.dor_lmb_pc_cm_vector_density_add`
- Exact Lean type: `∀ (P n : ℕ) (U : Set (Euclid P)) (R₁ R₂ R : IMRep U n) (T : GeometricCurrentOn U n), IsOpen U → R.Represents T → (∀ ω : TestFormOn U n, T ω = R₁.action (ω : DifferentialForm (Euclid P) n) + R₂.action (ω : DifferentialForm (Euclid P) n)) → ∀ᵐ x ∂μHE[n], R.carrier.indicator (fun y => (R.mult y : ℝ) • R.orient y) x = R₁.carrier.indicator (fun y => (R₁.mult y : ℝ) • R₁.orient y) x + R₂.carrier.indicator (fun y => (R₂.mult y : ℝ) • R₂.orient y) x`

## Sibling prerequisites

- `root.regular_set_dense-a1.integer_combination-a1.combination_construction-a1`
- `root.regular_set_dense-a1.integer_combination-a1.combination_action-a1`
- `root.half_space_cone_lies_in_boundary-a1.imrep_measure_unique-a1.vector_density_ae_eq-a1`

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
