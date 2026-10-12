# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.boundary_rectifiability-a1.zero_dim_weak_limit-a1.finite_dirac_im-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/nodes/root-boundary-rectifiability-a1-zero-dim-weak-limit-a1-finite-dirac-im-a1/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.boundary_rectifiability-a1.zero_dim_weak_limit-a1`
- Child key: `finite_dirac_im`
- Declaration: `Submission.br_zd_finite_dirac_im`
- Exact Lean type: `∀ (P : ℕ) (U : Set (Eucl P)) (D : Finset (Eucl P)) (a : Eucl P → ℤ), (↑D : Set (Eucl P)) ⊆ U → ∃ Y : GeometricCurrentOn U 0, IsIntegerMultiplicity Y ∧ ∀ ω : TestFormOn U 0, Y ω = ∑ x ∈ D, (a x : ℝ) * (ω : DifferentialForm (Eucl P) 0) x ![]`

## Sibling prerequisites

- None.

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
