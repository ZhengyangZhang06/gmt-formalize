# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.slicing-a1.slice_integer_multiplicity-a1.coarea-a1.chart_regular-a1.cover-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/nodes/root-slicing-a1-slice-integer-multiplicity-a1-coarea-a1-chart-regular-310b812607/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.slicing-a1.slice_integer_multiplicity-a1.coarea-a1.chart_regular-a1`
- Child key: `cover`
- Declaration: `Submission.slicing_im_creg_local_to_global`
- Exact Lean type: `∀ (P n : ℕ) (Φ : Eucl n → Eucl P) (Ω : Set (Eucl n)) (W : Set (Eucl P)) (f : Eucl P → ℝ) (J g : Eucl P → ℝ≥0∞) (μ ν : Measure (Eucl P)), IsOpen Ω → Continuous Φ → InjOn Φ Ω → Measurable f → MeasurableSet W → W ⊆ Φ '' Ω → (∀ w₀ ∈ Ω, Φ w₀ ∈ W → ∃ O : Set (Eucl n), IsOpen O ∧ w₀ ∈ O ∧ ∀ S : Set (Eucl n), MeasurableSet S → S ⊆ O ∩ (Ω ∩ Φ ⁻¹' W) → AEMeasurable (fun t : ℝ => ∫⁻ x in Φ '' S ∩ f ⁻¹' {t}, g x ∂ν) (volume : Measure ℝ) ∧ ∫⁻ t, (∫⁻ x in Φ '' S ∩ f ⁻¹' {t}, g x ∂ν) ∂(volume : Measure ℝ) = ∫⁻ x in Φ '' S, J x * g x ∂μ) → AEMeasurable (fun t : ℝ => ∫⁻ x in W ∩ f ⁻¹' {t}, g x ∂ν) (volume : Measure ℝ) ∧ ∫⁻ t, (∫⁻ x in W ∩ f ⁻¹' {t}, g x ∂ν) ∂(volume : Measure ℝ) = ∫⁻ x in W, J x * g x ∂μ`

## Sibling prerequisites

- None.

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
