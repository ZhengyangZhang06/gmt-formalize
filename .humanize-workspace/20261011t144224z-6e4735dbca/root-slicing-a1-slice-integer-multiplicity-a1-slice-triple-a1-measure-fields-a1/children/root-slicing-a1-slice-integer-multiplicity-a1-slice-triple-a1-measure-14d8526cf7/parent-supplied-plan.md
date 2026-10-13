# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.slicing-a1.slice_integer_multiplicity-a1.slice_triple-a1.measure_fields-a1.slice_integrable-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/nodes/root-slicing-a1-slice-integer-multiplicity-a1-slice-triple-a1-measure-14d8526cf7/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.slicing-a1.slice_integer_multiplicity-a1.slice_triple-a1.measure_fields-a1`
- Child key: `slice_integrable`
- Declaration: `Submission.slicing_im_st_mf_slice_integrable`
- Exact Lean type: `∀ (P m : ℕ) (U M : Set (Eucl P)) (θ : Eucl P → ℝ) (f : Eucl P → ℝ) (L : ℝ≥0) (G : Eucl P → Eucl P), IsOpen U → M ⊆ U → (∀ K : Set (Eucl P), IsCompact K → K ⊆ U → IntegrableOn θ (M ∩ K) (μHE[m + 1] : Measure (Eucl P))) → (∀ x, ‖G x‖ ≤ L) → (∀ g : Eucl P → ℝ≥0∞, Measurable g → AEMeasurable (fun t : ℝ => ∫⁻ x in M ∩ f ⁻¹' {t}, g x ∂(μHE[m] : Measure (Eucl P))) (volume : Measure ℝ) ∧ ∫⁻ t, (∫⁻ x in M ∩ f ⁻¹' {t}, g x ∂(μHE[m] : Measure (Eucl P))) ∂(volume : Measure ℝ) = ∫⁻ x in M, ‖G x‖ₑ * g x ∂(μHE[m + 1] : Measure (Eucl P))) → (∀ p : Eucl P → Prop, (∀ᵐ x ∂((μHE[m + 1] : Measure (Eucl P)).restrict M), p x) → ∀ᵐ t ∂(volume : Measure ℝ), ∀ᵐ x ∂((μHE[m] : Measure (Eucl P)).restrict (M ∩ f ⁻¹' {t})), p x) → ∀ᵐ t ∂(volume : Measure ℝ), ∀ K : Set (Eucl P), IsCompact K → K ⊆ U → IntegrableOn θ (M ∩ f ⁻¹' {t} ∩ K) (μHE[m] : Measure (Eucl P))`

## Sibling prerequisites

- `root.compactness_mass_bounds-a1.exhaustion-a1`

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
