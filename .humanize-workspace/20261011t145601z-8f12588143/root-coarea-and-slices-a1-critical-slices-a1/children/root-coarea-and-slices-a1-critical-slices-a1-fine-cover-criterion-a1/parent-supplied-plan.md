# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.coarea_and_slices-a1.critical_slices-a1.fine_cover_criterion-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T145601Z-8f12588143/nodes/root-coarea-and-slices-a1-critical-slices-a1-fine-cover-criterion-a1/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.coarea_and_slices-a1.critical_slices-a1`
- Child key: `fine_cover_criterion`
- Declaration: `Submission.critSlices_ae_slice_null_of_covers`
- Exact Lean type: `∀ (n m k : ℕ) (S : Set (Rn n)) (G : Rn n → Rn m), 0 < k → (∀ ε : ℝ≥0∞, 0 < ε → ∃ (ι : Type) (_ : Countable ι) (T : ι → Set (Rn n)), S ⊆ ⋃ i, T i ∧ (∀ i, Metric.ediam (T i) ≤ ε) ∧ ∑' i, Metric.ediam (T i) ^ k * volume (G '' (T i ∩ S)) ≤ ε) → ∀ᵐ y ∂(volume : Measure (Rn m)), μHE[k] (S ∩ G ⁻¹' {y}) = 0`

## Sibling prerequisites

- None.

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
