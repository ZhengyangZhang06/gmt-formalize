# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.slicing-a1.slice_integer_multiplicity-a1.coarea-a1.eilenberg-a1.near_optimal_cover-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/nodes/root-slicing-a1-slice-integer-multiplicity-a1-coarea-a1-eilenberg-a1-7f6e8f0ff4/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.slicing-a1.slice_integer_multiplicity-a1.coarea-a1.eilenberg-a1`
- Child key: `near_optimal_cover`
- Declaration: `Submission.slicing_im_coarea_eil_near_optimal_cover`
- Exact Lean type: `∀ (X : Type) [EMetricSpace X] [MeasurableSpace X] [BorelSpace X] (d : ℝ) (A : Set X) (r ε : ℝ≥0∞), 0 ≤ d → 0 < r → 0 < ε → (μH[d] : Measure X) A ≠ ∞ → ∃ S : ℕ → Set X, (∀ i, S i ⊆ A) ∧ A ⊆ ⋃ i, S i ∧ (∀ i, ediam (S i) ≤ r) ∧ ∑' i, ⨆ (_ : (S i).Nonempty), ediam (S i) ^ d ≤ (μH[d] : Measure X) A + ε`

## Sibling prerequisites

- None.

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
