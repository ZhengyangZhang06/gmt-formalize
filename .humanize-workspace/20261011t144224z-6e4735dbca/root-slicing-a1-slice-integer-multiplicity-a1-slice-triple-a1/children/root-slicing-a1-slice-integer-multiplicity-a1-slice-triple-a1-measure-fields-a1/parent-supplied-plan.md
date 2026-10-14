# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.slicing-a1.slice_integer_multiplicity-a1.slice_triple-a1.measure_fields-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/nodes/root-slicing-a1-slice-integer-multiplicity-a1-slice-triple-a1-measure-fields-a1/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.slicing-a1.slice_integer_multiplicity-a1.slice_triple-a1`
- Child key: `measure_fields`
- Declaration: `Submission.slicing_im_st_measure_fields`
- Exact Lean type: `∀ (P m : ℕ) (U M : Set (Eucl P)) (θ : Eucl P → ℝ) (ξ : Eucl P → NVector (Eucl P) (m + 1)) (f : Eucl P → ℝ) (L : ℝ≥0) (G : Eucl P → Eucl P), IsOpen U → IsRectifiableTriple U (m + 1) M θ ξ → Measurable f → Measurable G → (∀ x, ‖G x‖ ≤ L) → (∀ g : Eucl P → ℝ≥0∞, Measurable g → AEMeasurable (fun t : ℝ => ∫⁻ x in M ∩ f ⁻¹' {t}, g x ∂(μHE[m] : Measure (Eucl P))) (volume : Measure ℝ) ∧ ∫⁻ t, (∫⁻ x in M ∩ f ⁻¹' {t}, g x ∂(μHE[m] : Measure (Eucl P))) ∂(volume : Measure ℝ) = ∫⁻ x in M, ‖G x‖ₑ * g x ∂(μHE[m + 1] : Measure (Eucl P))) → ∀ᵐ t ∂(volume : Measure ℝ), NullMeasurableSet {x | x ∈ M ∧ f x = t ∧ G x ≠ 0} (μHE[m] : Measure (Eucl P)) ∧ (∀ K : Set (Eucl P), IsCompact K → K ⊆ U → IntegrableOn θ ({x | x ∈ M ∧ f x = t ∧ G x ≠ 0} ∩ K) (μHE[m] : Measure (Eucl P))) ∧ AEStronglyMeasurable (fun x => (ξ x).comp ((ContinuousAlternatingMap.alternatizeUncurryFinCLM ℝ (Eucl P) ℝ).comp (ContinuousLinearMap.smulRightL ℝ (Eucl P) (Covector (Eucl P) m) (innerSL ℝ (‖G x‖⁻¹ • G x))))) ((μHE[m] : Measure (Eucl P)).restrict {x | x ∈ M ∧ f x = t ∧ G x ≠ 0})`

## Sibling prerequisites

- `root.slicing-a1.slice_integer_multiplicity-a1.slice_triple-a1.ae_transfer-a1`

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
