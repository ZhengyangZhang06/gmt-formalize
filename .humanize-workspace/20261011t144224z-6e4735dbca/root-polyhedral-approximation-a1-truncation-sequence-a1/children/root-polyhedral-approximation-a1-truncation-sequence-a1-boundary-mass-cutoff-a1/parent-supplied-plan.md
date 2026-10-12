# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.polyhedral_approximation-a1.truncation_sequence-a1.boundary_mass_cutoff-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/nodes/root-polyhedral-approximation-a1-truncation-sequence-a1-boundary-mass-cutoff-a1/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.polyhedral_approximation-a1.truncation_sequence-a1`
- Child key: `boundary_mass_cutoff`
- Declaration: `Submission.polyhedral_approx_boundary_mass_cutoff`
- Exact Lean type: `∀ (P m : ℕ) (U₁ U₂ W V : Set (Eucl P)) (X : GeometricCurrentOn U₁ (m + 1)) (A : GeometricCurrentOn U₂ (m + 1)), IsOpen W → W ⊆ U₂ → IsCompact (closure V) → closure V ⊆ W → (∀ (η : TestFormOn U₁ (m + 1)) (η' : TestFormOn U₂ (m + 1)), (∀ x ∈ V, (η : DifferentialForm (Eucl P) (m + 1)) x = (η' : DifferentialForm (Eucl P) (m + 1)) x) → X η = A η') → X.boundary.mass ≤ A.boundary.massOn W`

## Sibling prerequisites

- None.

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
