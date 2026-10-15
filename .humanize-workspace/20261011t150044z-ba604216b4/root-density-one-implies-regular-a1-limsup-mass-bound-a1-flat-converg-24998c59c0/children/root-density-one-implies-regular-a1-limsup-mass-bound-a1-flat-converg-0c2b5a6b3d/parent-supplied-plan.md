# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.density_one_implies_regular-a1.limsup_mass_bound-a1.flat_convergence-a1.deformation-a1.cube_poincare-a1.median_deviation-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-density-one-implies-regular-a1-limsup-mass-bound-a1-flat-converg-0c2b5a6b3d/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.density_one_implies_regular-a1.limsup_mass_bound-a1.flat_convergence-a1.deformation-a1.cube_poincare-a1`
- Child key: `median_deviation`
- Declaration: `Submission.dor_lmb_fcd_cp_median_deviation`
- Exact Lean type: `∀ (P : ℕ) (W : Set (Euclid P)) (v : Euclid P → ℝ) (β θ : ℝ), MeasurableSet W → volume W ≠ ∞ → IntegrableOn v W → 0 < θ → θ * (volume W).toReal ≤ (volume (W ∩ {y | β ≤ v y})).toReal → θ * (volume W).toReal ≤ (volume (W ∩ {y | v y ≤ β})).toReal → ∫ y in W, |v y - β| ≤ (1 + θ⁻¹) * ((volume W).toReal)⁻¹ * ∫ x in W, ∫ y in W, |v x - v y|`

## Sibling prerequisites

- None.

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
