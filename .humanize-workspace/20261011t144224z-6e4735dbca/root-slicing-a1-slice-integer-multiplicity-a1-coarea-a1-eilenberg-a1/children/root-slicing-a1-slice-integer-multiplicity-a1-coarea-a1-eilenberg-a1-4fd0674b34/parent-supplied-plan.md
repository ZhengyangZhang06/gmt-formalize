# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.slicing-a1.slice_integer_multiplicity-a1.coarea-a1.eilenberg-a1.unnormalized-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/nodes/root-slicing-a1-slice-integer-multiplicity-a1-coarea-a1-eilenberg-a1-4fd0674b34/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.slicing-a1.slice_integer_multiplicity-a1.coarea-a1.eilenberg-a1`
- Child key: `unnormalized`
- Declaration: `Submission.slicing_im_coarea_eil_unnormalized`
- Exact Lean type: `∀ (X : Type) [EMetricSpace X] [MeasurableSpace X] [BorelSpace X] (m : ℕ) (f : X → ℝ) (L : ℝ≥0) (A : Set X), LipschitzOnWith L f A → ∃ ψ : ℝ → ℝ≥0∞, Measurable ψ ∧ (∀ t : ℝ, (μH[(m : ℝ)] : Measure X) (A ∩ f ⁻¹' {t}) ≤ ψ t) ∧ ∫⁻ t, ψ t ≤ 2 * (L : ℝ≥0∞) * (μH[((m + 1 : ℕ) : ℝ)] : Measure X) A`

## Sibling prerequisites

- `root.slicing-a1.slice_integer_multiplicity-a1.coarea-a1.eilenberg-a1.near_optimal_cover-a1`
- `root.slicing-a1.slice_integer_multiplicity-a1.coarea-a1.eilenberg-a1.liminf_cover_bound-a1`
- `root.slicing-a1.slice_integer_multiplicity-a1.coarea-a1.eilenberg-a1.cover_majorant-a1`

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
