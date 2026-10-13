# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.rectifiability-a1.bf_projection_null_ae-a1.infinite_fibre_null-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/nodes/root-rectifiability-a1-bf-projection-null-ae-a1-infinite-fibre-null-a1/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.rectifiability-a1.bf_projection_null_ae-a1`
- Child key: `infinite_fibre_null`
- Declaration: `Submission.rectifiability_bf_infinite_fibre_null`
- Exact Lean type: `∀ (N m : ℕ) (E : Set (Eucl N)) (f : Eucl N → Eucl (m + 1)) (K : ℝ≥0), MeasurableSet E → (μHE[m + 1] : Measure (Eucl N)) E < ∞ → LipschitzWith K f → (volume : Measure (Eucl (m + 1))) {y : Eucl (m + 1) | (E ∩ f ⁻¹' {y}).Infinite} = 0`

## Sibling prerequisites

- None.

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
