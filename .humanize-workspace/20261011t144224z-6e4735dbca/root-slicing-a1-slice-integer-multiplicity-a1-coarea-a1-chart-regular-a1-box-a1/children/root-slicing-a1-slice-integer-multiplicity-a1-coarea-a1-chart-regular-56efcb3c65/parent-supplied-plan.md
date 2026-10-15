# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.slicing-a1.slice_integer_multiplicity-a1.coarea-a1.chart_regular-a1.box-a1.integrand_measurable-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/nodes/root-slicing-a1-slice-integer-multiplicity-a1-coarea-a1-chart-regular-56efcb3c65/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.slicing-a1.slice_integer_multiplicity-a1.coarea-a1.chart_regular-a1.box-a1`
- Child key: `integrand_measurable`
- Declaration: `Submission.slicing_im_creg_box_integrand_measurable`
- Exact Lean type: `∀ (P m : ℕ) (Φ : Eucl (m + 1) → Eucl P) (B : Set (Eucl (m + 1))) (χ : Eucl (m + 1) → Eucl (m + 1)) (S : Set (Eucl (m + 1))) (g : Eucl P → ℝ≥0∞), ContDiff ℝ 1 Φ → IsOpen B → ContDiffOn ℝ 1 χ B → MeasurableSet S → Measurable g → Measurable ((B ∩ χ ⁻¹' S).indicator (fun y => g (Φ (χ y)) * ENNReal.ofReal (Real.sqrt (Matrix.of fun i j : Fin m => inner ℝ (fderiv ℝ Φ (χ y) (fderiv ℝ χ y (EuclideanSpace.single i.succ 1))) (fderiv ℝ Φ (χ y) (fderiv ℝ χ y (EuclideanSpace.single j.succ 1)))).det)))`

## Sibling prerequisites

- None.

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
