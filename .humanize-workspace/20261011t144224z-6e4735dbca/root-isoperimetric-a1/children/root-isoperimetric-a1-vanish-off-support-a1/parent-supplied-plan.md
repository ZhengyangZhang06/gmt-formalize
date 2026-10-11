# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.isoperimetric-a1.vanish_off_support-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/nodes/root-isoperimetric-a1-vanish-off-support-a1/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.isoperimetric-a1`
- Child key: `vanish_off_support`
- Declaration: `Submission.isoperimetric_apply_eq_zero_of_disjoint_support`
- Exact Lean type: `∀ (P n : ℕ) (U : Set (Eucl P)) (T : GeometricCurrentOn U n) (ω : TestFormOn U n), Disjoint (tsupport (ω : DifferentialForm (Eucl P) n)) T.support → T ω = 0`

## Sibling prerequisites

- None.

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
