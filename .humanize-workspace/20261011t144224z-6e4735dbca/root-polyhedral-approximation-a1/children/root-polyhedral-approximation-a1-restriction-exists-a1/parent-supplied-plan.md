# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.polyhedral_approximation-a1.restriction_exists-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/nodes/root-polyhedral-approximation-a1-restriction-exists-a1/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.polyhedral_approximation-a1`
- Child key: `restriction_exists`
- Declaration: `Submission.polyhedral_approx_restriction_exists`
- Exact Lean type: `∀ (P n : ℕ) (U : Set (Eucl P)), IsOpen U → ∀ T : GeometricCurrentOn U n, (∀ (μ : Measure (Eucl P)) (v : Eucl P → NVector (Eucl P) n), IsMeasureRepresentation T μ v → ∀ A : Set (Eucl P), MeasurableSet A → ∃ S : GeometricCurrentOn U n, IsRestriction T A S) ∧ ∀ (A : Set (Eucl P)) (S : GeometricCurrentOn U n), IsRestriction T A S → ∀ W : Set (Eucl P), CompactlyContainedOpen W U → S.massOn W < ∞`

## Sibling prerequisites

- `root.polyhedral_approximation-a1.pairing_expansion-a1`

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
