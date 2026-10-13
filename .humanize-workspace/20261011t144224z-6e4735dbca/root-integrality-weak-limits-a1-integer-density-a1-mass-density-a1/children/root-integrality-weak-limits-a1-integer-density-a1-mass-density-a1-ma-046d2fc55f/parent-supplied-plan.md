# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.integrality_weak_limits-a1.integer_density-a1.mass_density-a1.mass_measure_balls-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/nodes/root-integrality-weak-limits-a1-integer-density-a1-mass-density-a1-ma-046d2fc55f/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.integrality_weak_limits-a1.integer_density-a1.mass_density-a1`
- Child key: `mass_measure_balls`
- Declaration: `Submission.ind_md_mass_measure_balls`
- Exact Lean type: `∀ (P n : ℕ) (T : GeometricCurrentOn (univ : Set (Eucl P)) n), T.mass < ∞ → ∃ μ : Measure (Eucl P), μ univ ≤ T.mass ∧ ∀ (x : Eucl P) (r : ℝ), μ (ball x r) = T.massOn (ball x r)`

## Sibling prerequisites

- None.

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
