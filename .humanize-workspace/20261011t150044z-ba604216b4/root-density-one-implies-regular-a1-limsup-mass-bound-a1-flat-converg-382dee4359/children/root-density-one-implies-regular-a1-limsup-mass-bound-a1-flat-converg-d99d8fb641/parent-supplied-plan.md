# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.density_one_implies_regular-a1.limsup_mass_bound-a1.flat_convergence-a1.deformation_top-a1.isometric_pushforward-a1.change_of_variables-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-density-one-implies-regular-a1-limsup-mass-bound-a1-flat-converg-d99d8fb641/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.density_one_implies_regular-a1.limsup_mass_bound-a1.flat_convergence-a1.deformation_top-a1.isometric_pushforward-a1`
- Child key: `change_of_variables`
- Declaration: `Submission.dor_lmb_fc_dtop_ip_isometry_change_of_variables`
- Exact Lean type: `∀ (P Q d : ℕ) (f : Euclid P → Euclid Q), Isometry f → MeasurableEmbedding f ∧ (∀ A : Set (Euclid P), Measure.map f ((μHE[d] : Measure (Euclid P)).restrict A) = (μHE[d] : Measure (Euclid Q)).restrict (f '' A)) ∧ (∀ (A : Set (Euclid P)) (g : Euclid Q → ℝ), ∫ y in f '' A, g y ∂μHE[d] = ∫ x in A, g (f x) ∂μHE[d]) ∧ ∀ (A : Set (Euclid P)) (g : Euclid Q → ℝ≥0∞), ∫⁻ y in f '' A, g y ∂μHE[d] = ∫⁻ x in A, g (f x) ∂μHE[d]`

## Sibling prerequisites

- None.

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
