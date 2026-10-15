# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.density_one_implies_regular-a1.limsup_mass_bound-a1.borel_restriction-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-density-one-implies-regular-a1-limsup-mass-bound-a1-borel-restriction-a1/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.density_one_implies_regular-a1.limsup_mass_bound-a1`
- Child key: `borel_restriction`
- Declaration: `Submission.dor_lmb_imrep_restrict_current`
- Exact Lean type: `∀ (P n : ℕ) (U A : Set (Euclid P)) (R : IMRep U n), IsOpen U → MeasurableSet A → ∃ (S : GeometricCurrentOn U n) (R' : IMRep U n), R'.Represents S ∧ R'.carrier = R.carrier ∩ A ∧ R'.mult = R.mult ∧ R'.orient = R.orient ∧ R'.measure = R.measure.restrict A`

## Sibling prerequisites

- `root.density_one_implies_regular-a1.limsup_mass_bound-a1.tangent_locality-a1`

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
