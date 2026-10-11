# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.polyhedral_approximation-a1.restriction_tau-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/nodes/root-polyhedral-approximation-a1-restriction-tau-a1/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.polyhedral_approximation-a1`
- Child key: `restriction_tau`
- Declaration: `Submission.polyhedral_approx_restriction_tau`
- Exact Lean type: `∀ (P n : ℕ) (U : Set (Eucl P)), IsOpen U → ∀ (T : GeometricCurrentOn U n) (M : Set (Eucl P)) (θ : Eucl P → ℝ) (ξ : Eucl P → NVector (Eucl P) n), IsRectifiableTriple U n M θ ξ → (∀ ω : TestFormOn U n, T ω = tauAction n M θ ξ ω) → ∀ (A : Set (Eucl P)) (S : GeometricCurrentOn U n), IsRestriction T A S → ∀ ω : TestFormOn U n, S ω = tauAction n (M ∩ A) θ ξ ω`

## Sibling prerequisites

- `root.polyhedral_approximation-a1.pairing_expansion-a1`
- `root.polyhedral_approximation-a1.measure_uniqueness-a1`

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
