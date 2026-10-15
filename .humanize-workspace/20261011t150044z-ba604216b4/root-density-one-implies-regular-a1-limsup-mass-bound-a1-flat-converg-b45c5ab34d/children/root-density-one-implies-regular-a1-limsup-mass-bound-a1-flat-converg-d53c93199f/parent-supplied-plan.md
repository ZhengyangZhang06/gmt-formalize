# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.density_one_implies_regular-a1.limsup_mass_bound-a1.flat_convergence-a1.deformation_top-a1.cube_chain_im-a1.borel_current_im-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-density-one-implies-regular-a1-limsup-mass-bound-a1-flat-converg-d53c93199f/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.density_one_implies_regular-a1.limsup_mass_bound-a1.flat_convergence-a1.deformation_top-a1.cube_chain_im-a1`
- Child key: `borel_current_im`
- Declaration: `Submission.dor_lmb_fc_dtop_cci_borel_current_im`
- Exact Lean type: `∀ (n : ℕ) (G : Set (Euclid n)), MeasurableSet G → ∃ A : GeometricCurrentOn (univ : Set (Euclid n)) n, IsIntegerMultiplicity A ∧ ∀ ω : TestFormOn (univ : Set (Euclid n)) n, A ω = ∫ x in G, (ω : DifferentialForm (Euclid n) n) x (fun k => EuclideanSpace.single k (1 : ℝ)) ∂μHE[n]`

## Sibling prerequisites

- `root.compactness_of_minimizing_currents-a1.im_calculus-a1`

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
