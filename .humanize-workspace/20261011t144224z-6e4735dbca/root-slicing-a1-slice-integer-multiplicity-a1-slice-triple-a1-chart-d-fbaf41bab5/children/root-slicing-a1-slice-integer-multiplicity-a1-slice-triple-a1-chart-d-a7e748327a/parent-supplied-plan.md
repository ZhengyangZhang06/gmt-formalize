# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.slicing-a1.slice_integer_multiplicity-a1.slice_triple-a1.chart_data-a1.c1_cover-a1.singular_compression-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/nodes/root-slicing-a1-slice-integer-multiplicity-a1-slice-triple-a1-chart-d-a7e748327a/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.slicing-a1.slice_integer_multiplicity-a1.slice_triple-a1.chart_data-a1.c1_cover-a1`
- Child key: `singular_compression`
- Declaration: `Submission.slicing_im_st_cd_c1c_singular_compression`
- Exact Lean type: `∀ (n P : ℕ) (f : Eucl n → Eucl P) (A : Eucl n →L[ℝ] Eucl P) (S : Set (Eucl n)) (t : ℝ≥0), 0 < t → t ≤ 1 → ¬ Function.Injective A → ApproximatesLinearOn f A S (t ^ 2) → (μHE[n] : Measure (Eucl P)) (f '' S) ≤ ((‖A‖₊ + t : ℝ≥0) : ℝ≥0∞) ^ n * ((t : ℝ≥0∞) * (volume : Measure (Eucl n)) S)`

## Sibling prerequisites

- None.

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
