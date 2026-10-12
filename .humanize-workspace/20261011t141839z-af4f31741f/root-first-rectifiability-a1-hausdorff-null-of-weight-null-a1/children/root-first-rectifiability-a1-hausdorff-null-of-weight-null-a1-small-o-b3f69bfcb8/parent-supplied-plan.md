# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.first_rectifiability-a1.hausdorff_null_of_weight_null-a1.small_open_superset-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T141839Z-af4f31741f/nodes/root-first-rectifiability-a1-hausdorff-null-of-weight-null-a1-small-o-b3f69bfcb8/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.first_rectifiability-a1.hausdorff_null_of_weight_null-a1`
- Child key: `small_open_superset`
- Declaration: `Submission.frt_hnw_exists_open_superset_measure_lt`
- Exact Lean type: `∀ (N : ℕ) (μ : Measure (Euclidean N)) (U Z : Set (Euclidean N)) (ζ : ℝ≥0∞), IsOpen U → (∀ K : Set (Euclidean N), IsCompact K → K ⊆ U → μ K ≠ ∞) → Z ⊆ U → μ Z = 0 → 0 < ζ → ∃ O : Set (Euclidean N), IsOpen O ∧ Z ⊆ O ∧ O ⊆ U ∧ μ O < ζ`

## Sibling prerequisites

- None.

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
