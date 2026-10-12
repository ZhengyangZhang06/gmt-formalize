# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.slicing-a1.slice_integer_multiplicity-a1.coarea-a1.chart_regular-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/nodes/root-slicing-a1-slice-integer-multiplicity-a1-coarea-a1-chart-regular-a1/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.slicing-a1.slice_integer_multiplicity-a1.coarea-a1`
- Child key: `chart_regular`
- Declaration: `Submission.slicing_im_coarea_chart_regular`
- Exact Lean type: `∀ (P m : ℕ) (Φ : Eucl (m + 1) → Eucl P) (Ω : Set (Eucl (m + 1))) (h : Eucl (m + 1) → ℝ) (f : Eucl P → ℝ) (G : Eucl P → Eucl P) (W : Set (Eucl P)), IsOpen Ω → ContDiff ℝ 1 Φ → (∃ K : ℝ≥0, LipschitzOnWith K Φ Ω) → (∃ c : ℝ, 0 < c ∧ ∀ w ∈ Ω, ∀ w' ∈ Ω, c * ‖w - w'‖ ≤ ‖Φ w - Φ w'‖) → ContDiff ℝ 1 h → Measurable f → Measurable G → MeasurableSet W → W ⊆ Φ '' Ω → (∀ w ∈ Ω, Φ w ∈ W → f (Φ w) = h w ∧ G (Φ w) ≠ 0 ∧ G (Φ w) ∈ LinearMap.range (fderiv ℝ Φ w).toLinearMap ∧ ∀ u, inner ℝ (G (Φ w)) (fderiv ℝ Φ w u) = fderiv ℝ h w u) → ∀ g : Eucl P → ℝ≥0∞, Measurable g → AEMeasurable (fun t : ℝ => ∫⁻ x in W ∩ f ⁻¹' {t}, g x ∂(μHE[m] : Measure (Eucl P))) (volume : Measure ℝ) ∧ ∫⁻ t, (∫⁻ x in W ∩ f ⁻¹' {t}, g x ∂(μHE[m] : Measure (Eucl P))) ∂(volume : Measure ℝ) = ∫⁻ x in W, ‖G x‖ₑ * g x ∂(μHE[m + 1] : Measure (Eucl P))`

## Sibling prerequisites

- `root.slicing-a1.slice_integer_multiplicity-a1.coarea-a1.glue-a1`

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
