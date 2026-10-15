# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.rectifiability-a1.projection_null-a1.borel_null-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/nodes/root-rectifiability-a1-projection-null-a1-borel-null-a1/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.rectifiability-a1.projection_null-a1`
- Child key: `borel_null`
- Declaration: `Submission.rpn_null_of_compact_null`
- Exact Lean type: `∀ (P : ℕ) (U E : Set (Eucl P)) (μ : Measure (Eucl P)), IsOpen U → μ Uᶜ = 0 → (∀ W, CompactlyContainedOpen W U → μ W < ∞) → MeasurableSet E → (∀ K, IsCompact K → K ⊆ E → K ⊆ U → μ K = 0) → μ E = 0`

## Sibling prerequisites

- None.

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
