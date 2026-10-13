# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.isoperimetric-a1.finite_mass-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/nodes/root-isoperimetric-a1-finite-mass-a1/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.isoperimetric-a1`
- Child key: `finite_mass`
- Declaration: `Submission.isoperimetric_mass_lt_top`
- Exact Lean type: `∀ (P n : ℕ) (T : GeometricCurrentOn (univ : Set (Eucl P)) n), IsIntegerMultiplicity T → IsCompact T.support → T.mass < ∞`

## Sibling prerequisites

- `root.isoperimetric-a1.vanish_off_support-a1`
- `root.isoperimetric-a1.covector_eval_bound-a1`

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
