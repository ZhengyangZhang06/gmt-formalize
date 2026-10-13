# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.slicing-a1.slice_integer_multiplicity-a1.coarea-a1.chart_regular-a1.box-a1.bulk-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/nodes/root-slicing-a1-slice-integer-multiplicity-a1-coarea-a1-chart-regular-cf6d5a08c5/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.slicing-a1.slice_integer_multiplicity-a1.coarea-a1.chart_regular-a1.box-a1`
- Child key: `bulk`
- Declaration: `Submission.slicing_im_creg_box_bulk`
- Exact Lean type: `∀ (P n : ℕ) (Φ : Eucl n → Eucl P) (Ω : Set (Eucl n)) (B : Set (Eucl n)) (χ : Eucl n → Eucl n) (S : Set (Eucl n)) (ψ : Eucl P → ℝ≥0∞), IsOpen Ω → (∃ K : ℝ≥0, LipschitzOnWith K Φ Ω) → (∃ c : ℝ, 0 < c ∧ ∀ w ∈ Ω, ∀ w' ∈ Ω, c * ‖w - w'‖ ≤ ‖Φ w - Φ w'‖) → IsOpen B → ContDiffOn ℝ 1 χ B → InjOn χ B → χ '' B ⊆ Ω → MeasurableSet S → S ⊆ χ '' B → Measurable ψ → ∫⁻ x in Φ '' S, ψ x ∂(μHE[n] : Measure (Eucl P)) = ∫⁻ y, (B ∩ χ ⁻¹' S).indicator (fun y => ENNReal.ofReal |(fderiv ℝ χ y).det| * (ψ (Φ (χ y)) * ENNReal.ofReal (Real.sqrt (Matrix.of fun i j => inner ℝ (fderiv ℝ Φ (χ y) (EuclideanSpace.single i 1)) (fderiv ℝ Φ (χ y) (EuclideanSpace.single j 1))).det))) y ∂(volume : Measure (Eucl n))`

## Sibling prerequisites

- `root.lipschitz_pushforward_im-a1.rectifiable_area_formula-a1.chart_change_of_variables-a1`

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
