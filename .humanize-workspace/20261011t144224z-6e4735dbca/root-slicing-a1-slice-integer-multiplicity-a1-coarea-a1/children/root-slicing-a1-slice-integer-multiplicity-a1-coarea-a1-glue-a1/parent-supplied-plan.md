# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.slicing-a1.slice_integer_multiplicity-a1.coarea-a1.glue-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/nodes/root-slicing-a1-slice-integer-multiplicity-a1-coarea-a1-glue-a1/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.slicing-a1.slice_integer_multiplicity-a1.coarea-a1`
- Child key: `glue`
- Declaration: `Submission.slicing_im_coarea_glue`
- Exact Lean type: `∀ (X : Type) [MeasurableSpace X] (μ ν : Measure X) (f : X → ℝ) (J g : X → ℝ≥0∞) (M : Set X) (W : ℕ → Set X), Measurable f → (∀ i, MeasurableSet (W i)) → (∀ i, W i ⊆ M) → Pairwise (Function.onFun Disjoint W) → (∀ᵐ x ∂(μ.restrict (M \ ⋃ i, W i)), J x * g x = 0) → (∀ᵐ t ∂(volume : Measure ℝ), ν ((M \ ⋃ i, W i) ∩ f ⁻¹' {t}) = 0) → (∀ i, AEMeasurable (fun t : ℝ => ∫⁻ x in W i ∩ f ⁻¹' {t}, g x ∂ν) (volume : Measure ℝ) ∧ ∫⁻ t, (∫⁻ x in W i ∩ f ⁻¹' {t}, g x ∂ν) ∂(volume : Measure ℝ) = ∫⁻ x in W i, J x * g x ∂μ) → AEMeasurable (fun t : ℝ => ∫⁻ x in M ∩ f ⁻¹' {t}, g x ∂ν) (volume : Measure ℝ) ∧ ∫⁻ t, (∫⁻ x in M ∩ f ⁻¹' {t}, g x ∂ν) ∂(volume : Measure ℝ) = ∫⁻ x in M, J x * g x ∂μ`

## Sibling prerequisites

- None.

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
