# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.gauss_green-a1.variation_formula-a1.vector_lusin-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T145601Z-8f12588143/nodes/root-gauss-green-a1-variation-formula-a1-vector-lusin-a1/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.gauss_green-a1.variation_formula-a1`
- Child key: `vector_lusin`
- Declaration: `Submission.gaussGreenVar_lusin_closed_subset_continuousOn`
- Exact Lean type: `∀ (N : ℕ) (μ : Measure (Rn N)) (f : Rn N → Rn N) (A : Set (Rn N)), Measurable f → MeasurableSet A → μ A ≠ ∞ → ∀ ε : ℝ≥0∞, 0 < ε → ∃ C ⊆ A, IsClosed C ∧ μ (A \ C) < ε ∧ ContinuousOn f C`

## Sibling prerequisites

- None.

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
