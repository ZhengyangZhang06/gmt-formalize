# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.slicing-a1.slice_integer_multiplicity-a1.coarea-a1.chart_critical-a1.null_of_small_majorants-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/nodes/root-slicing-a1-slice-integer-multiplicity-a1-coarea-a1-chart-critica-037f0b58df/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.slicing-a1.slice_integer_multiplicity-a1.coarea-a1.chart_critical-a1`
- Child key: `null_of_small_majorants`
- Declaration: `Submission.slicing_im_coarea_cc_null_of_small_majorants`
- Exact Lean type: `∀ (X : Type) [MeasurableSpace X] (ν : Measure X) (f : X → ℝ) (S : Set X) (M : ℝ≥0∞), M ≠ ∞ → (∀ ε : ℝ≥0, 0 < ε → ∃ (A : ℕ → Set X) (φ : ℕ → ℝ → ℝ≥0∞), S ⊆ ⋃ k, A k ∧ (∀ k, Measurable (φ k)) ∧ (∀ k t, ν (A k ∩ f ⁻¹' {t}) ≤ φ k t) ∧ ∑' k, ∫⁻ t, φ k t ≤ (ε : ℝ≥0∞) * M) → ∀ᵐ t ∂(volume : Measure ℝ), ν (S ∩ f ⁻¹' {t}) = 0`

## Sibling prerequisites

- None.

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
