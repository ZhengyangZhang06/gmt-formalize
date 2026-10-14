# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.slicing-a1.slice_integer_multiplicity-a1.coarea-a1.chart_critical-a1.small_lip_partition-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/nodes/root-slicing-a1-slice-integer-multiplicity-a1-coarea-a1-chart-critica-5fce30ee24/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.slicing-a1.slice_integer_multiplicity-a1.coarea-a1.chart_critical-a1`
- Child key: `small_lip_partition`
- Declaration: `Submission.slicing_im_coarea_cc_small_lip_partition`
- Exact Lean type: `∀ (n : ℕ) (h : Eucl n → ℝ) (E : Set (Eucl n)) (ε : ℝ≥0), ContDiff ℝ 1 h → MeasurableSet E → (∀ w ∈ E, fderiv ℝ h w = 0) → 0 < ε → ∃ D : ℕ → Set (Eucl n), (∀ k, MeasurableSet (D k)) ∧ Pairwise (Function.onFun Disjoint D) ∧ (⋃ k, D k) = E ∧ ∀ k, LipschitzOnWith ε h (D k)`

## Sibling prerequisites

- None.

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
