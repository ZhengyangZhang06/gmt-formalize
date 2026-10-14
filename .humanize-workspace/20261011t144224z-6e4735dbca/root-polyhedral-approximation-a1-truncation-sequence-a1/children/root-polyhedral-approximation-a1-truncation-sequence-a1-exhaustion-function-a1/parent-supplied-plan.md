# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.polyhedral_approximation-a1.truncation_sequence-a1.exhaustion_function-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/nodes/root-polyhedral-approximation-a1-truncation-sequence-a1-exhaustion-function-a1/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.polyhedral_approximation-a1.truncation_sequence-a1`
- Child key: `exhaustion_function`
- Declaration: `Submission.polyhedral_approx_exhaustion_function`
- Exact Lean type: `∀ (P : ℕ) (U : Set (Eucl P)), IsOpen U → ∃ φ : Eucl P → ℝ, LipschitzWith 1 φ ∧ (∀ t : ℝ, 0 < t → IsCompact {x | t ≤ φ x} ∧ {x | t ≤ φ x} ⊆ U) ∧ ∀ K : Set (Eucl P), IsCompact K → K ⊆ U → ∃ δ : ℝ, 0 < δ ∧ ∀ x ∈ K, δ ≤ φ x`

## Sibling prerequisites

- None.

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
