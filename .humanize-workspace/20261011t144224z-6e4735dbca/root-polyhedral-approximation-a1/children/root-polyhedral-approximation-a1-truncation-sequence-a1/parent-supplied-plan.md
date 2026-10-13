# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.polyhedral_approximation-a1.truncation_sequence-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/nodes/root-polyhedral-approximation-a1-truncation-sequence-a1/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.polyhedral_approximation-a1`
- Child key: `truncation_sequence`
- Declaration: `Submission.polyhedral_approx_truncation_seq`
- Exact Lean type: `SlicingTheorem → ∀ (P m : ℕ) (U : Set (Eucl P)), IsOpen U → ∀ T : GeometricCurrentOn U (m + 1), IsIntegerMultiplicity T → (∀ W, CompactlyContainedOpen W U → T.massOn W < ∞ ∧ T.boundary.massOn W < ∞) → ∃ X : ℕ → GeometricCurrentOn (univ : Set (Eucl P)) (m + 1), (∀ k, IsIntegerMultiplicity (X k)) ∧ (∀ k, (X k).mass + (X k).boundary.mass < ∞) ∧ ∀ ω : TestFormOn U (m + 1), ∀ᶠ k in atTop, X k (testFormOnInclusion (subset_univ U) (m + 1) ω) = T ω`

## Sibling prerequisites

- `root.polyhedral_approximation-a1.restriction_exists-a1`
- `root.polyhedral_approximation-a1.restriction_tau-a1`
- `root.polyhedral_approximation-a1.open_truncation-a1`

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
