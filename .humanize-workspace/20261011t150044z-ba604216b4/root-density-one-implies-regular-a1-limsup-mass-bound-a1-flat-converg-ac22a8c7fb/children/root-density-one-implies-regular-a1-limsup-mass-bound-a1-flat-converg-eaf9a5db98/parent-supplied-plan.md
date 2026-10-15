# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.density_one_implies_regular-a1.limsup_mass_bound-a1.flat_convergence-a1.im_series-a1.density_series-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-density-one-implies-regular-a1-limsup-mass-bound-a1-flat-converg-eaf9a5db98/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.density_one_implies_regular-a1.limsup_mass_bound-a1.flat_convergence-a1.im_series-a1`
- Child key: `density_series`
- Declaration: `Submission.dor_lmb_fc_ims_density_series`
- Exact Lean type: `∀ (P n : ℕ) (U : Set (Euclid P)) (R : ℕ → IMRep U n), ∑' r, (R r).measure U ≠ ∞ → ∃ η : Euclid P → MultiVector P n, (∀ᵐ x ∂μHE[n], HasSum (fun r => (R r).carrier.indicator (fun y => ((R r).mult y : ℝ) • (R r).orient y) x) (η x)) ∧ ∀ ω : TestFormOn U n, HasSum (fun r => (R r).action (ω : DifferentialForm (Euclid P) n)) (∫ x, η x ((ω : DifferentialForm (Euclid P) n) x) ∂μHE[n])`

## Sibling prerequisites

- `root.half_space_cone_lies_in_boundary-a1.imrep_measure_unique-a1.orientation_norm_bound-a1`

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
