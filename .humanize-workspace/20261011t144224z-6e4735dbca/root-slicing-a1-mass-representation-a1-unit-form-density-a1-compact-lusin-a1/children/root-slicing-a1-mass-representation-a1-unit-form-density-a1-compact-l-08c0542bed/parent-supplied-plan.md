# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.slicing-a1.mass_representation-a1.unit_form_density-a1.compact_lusin-a1.vector_lusin-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/nodes/root-slicing-a1-mass-representation-a1-unit-form-density-a1-compact-l-08c0542bed/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.slicing-a1.mass_representation-a1.unit_form_density-a1.compact_lusin-a1`
- Child key: `vector_lusin`
- Declaration: `Submission.smr_ufd_cl_vector_lusin`
- Exact Lean type: `∀ (P N : ℕ) (μ : Measure (Eucl P)) (u : Eucl P → EuclideanSpace ℝ (Fin N)), Measurable u → ∀ A : Set (Eucl P), MeasurableSet A → μ A ≠ ∞ → ∀ ε : ℝ≥0∞, ε ≠ 0 → ∃ C : Set (Eucl P), IsCompact C ∧ C ⊆ A ∧ μ (A \ C) < ε ∧ ContinuousOn u C`

## Sibling prerequisites

- None.

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
