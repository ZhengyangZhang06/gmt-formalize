# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.slicing-a1.slice_integer_multiplicity-a1.coarea-a1.eilenberg-a1.cover_majorant-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/nodes/root-slicing-a1-slice-integer-multiplicity-a1-coarea-a1-eilenberg-a1-8bffc3f0b1/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.slicing-a1.slice_integer_multiplicity-a1.coarea-a1.eilenberg-a1`
- Child key: `cover_majorant`
- Declaration: `Submission.slicing_im_coarea_eil_cover_majorant`
- Exact Lean type: `∀ (X : Type) [EMetricSpace X] (m : ℕ) (f : X → ℝ) (L : ℝ≥0) (A : Set X) (S : ℕ → Set X), LipschitzOnWith L f A → (∀ i, S i ⊆ A) → ∃ ψ : ℝ → ℝ≥0∞, Measurable ψ ∧ (∀ t : ℝ, ∑' i, ⨆ (_ : (S i ∩ (A ∩ f ⁻¹' {t})).Nonempty), ediam (S i ∩ (A ∩ f ⁻¹' {t})) ^ (m : ℝ) ≤ ψ t) ∧ ∫⁻ t, ψ t ≤ 2 * (L : ℝ≥0∞) * ∑' i, ⨆ (_ : (S i).Nonempty), ediam (S i) ^ ((m + 1 : ℕ) : ℝ)`

## Sibling prerequisites

- None.

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
