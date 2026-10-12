# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.boundary_rectifiability-a1.lattice_approximation-a1.mass_estimate-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/nodes/root-boundary-rectifiability-a1-lattice-approximation-a1-mass-estimate-a1/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.boundary_rectifiability-a1.lattice_approximation-a1`
- Child key: `mass_estimate`
- Declaration: `Submission.br_la_abs_apply_le_mul_mass`
- Exact Lean type: `∀ (P n : ℕ) (U : Set (Eucl P)) (Y : GeometricCurrentOn U n) (ω : TestFormOn U n) (C : ℝ), 0 < C → (∀ x : Eucl P, covectorEuclideanNorm ((ω : DifferentialForm (Eucl P) n) x) ≤ C) → Y.mass ≠ ∞ → |Y ω| ≤ C * Y.mass.toReal`

## Sibling prerequisites

- None.

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
