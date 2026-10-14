# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.dimension_reduction_results-a1.cone_splitting-a1.measure_invariance-a1.translate_invariance-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-dimension-reduction-results-a1-cone-splitting-a1-measure-invaria-dd69026a20/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.dimension_reduction_results-a1.cone_splitting-a1.measure_invariance-a1`
- Child key: `translate_invariance`
- Declaration: `Submission.dimred_cs_mi_withDensity_translate`
- Exact Lean type: `∀ (P n : ℕ) (f : Euclid P → ℝ≥0∞) (y : Euclid P), (∀ x : Euclid P, f (y + x) = f x) → ∀ A : Set (Euclid P), MeasurableSet A → (μHE[n] : Measure (Euclid P)).withDensity f ((fun x => y + x) ⁻¹' A) = (μHE[n] : Measure (Euclid P)).withDensity f A`

## Sibling prerequisites

- None.

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
