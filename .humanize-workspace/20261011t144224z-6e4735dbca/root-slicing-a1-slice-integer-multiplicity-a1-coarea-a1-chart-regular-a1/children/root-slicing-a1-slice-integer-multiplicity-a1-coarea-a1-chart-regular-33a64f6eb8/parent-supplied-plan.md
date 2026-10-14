# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.slicing-a1.slice_integer_multiplicity-a1.coarea-a1.chart_regular-a1.tonelli-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/nodes/root-slicing-a1-slice-integer-multiplicity-a1-coarea-a1-chart-regular-33a64f6eb8/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.slicing-a1.slice_integer_multiplicity-a1.coarea-a1.chart_regular-a1`
- Child key: `tonelli`
- Declaration: `Submission.slicing_im_creg_lintegral_cons`
- Exact Lean type: `∀ (m : ℕ) (F : Eucl (m + 1) → ℝ≥0∞), Measurable F → Measurable (fun t : ℝ => ∫⁻ v : Eucl m, F ((EuclideanSpace.equiv (Fin (m + 1)) ℝ).symm (Fin.cons t (EuclideanSpace.equiv (Fin m) ℝ v)))) ∧ ∫⁻ y, F y = ∫⁻ t : ℝ, ∫⁻ v : Eucl m, F ((EuclideanSpace.equiv (Fin (m + 1)) ℝ).symm (Fin.cons t (EuclideanSpace.equiv (Fin m) ℝ v)))`

## Sibling prerequisites

- None.

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
