# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.polyhedral_approximation-a1.open_truncation-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/nodes/root-polyhedral-approximation-a1-open-truncation-a1/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.polyhedral_approximation-a1`
- Child key: `open_truncation`
- Declaration: `Submission.polyhedral_approx_open_truncation`
- Exact Lean type: `∀ (P n : ℕ) (U V M : Set (Eucl P)) (θ : Eucl P → ℝ) (ξ : Eucl P → NVector (Eucl P) n), IsRectifiableTriple U n M θ ξ → (∀ x ∈ M, ∃ k : ℕ, θ x = k) → CompactlyContainedOpen V U → ∃ X : GeometricCurrentOn (univ : Set (Eucl P)) n, IsIntegerMultiplicity X ∧ X.mass < ∞ ∧ ∀ ω : TestFormOn (univ : Set (Eucl P)) n, X ω = tauAction n (M ∩ V) θ ξ ω`

## Sibling prerequisites

- `root.polyhedral_approximation-a1.pairing_expansion-a1`

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
