# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.slicing-a1.slice_integer_multiplicity-a1.slice_triple-a1.measure_fields-a1.slice_orientation_aesm-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/nodes/root-slicing-a1-slice-integer-multiplicity-a1-slice-triple-a1-measure-ae11d089ba/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.slicing-a1.slice_integer_multiplicity-a1.slice_triple-a1.measure_fields-a1`
- Child key: `slice_orientation_aesm`
- Declaration: `Submission.slicing_im_st_mf_slice_orientation_aesm`
- Exact Lean type: `∀ (P m : ℕ) (M : Set (Eucl P)) (ξ : Eucl P → NVector (Eucl P) (m + 1)) (f : Eucl P → ℝ) (G : Eucl P → Eucl P), AEStronglyMeasurable ξ ((μHE[m + 1] : Measure (Eucl P)).restrict M) → Measurable G → (∀ p : Eucl P → Prop, (∀ᵐ x ∂((μHE[m + 1] : Measure (Eucl P)).restrict M), p x) → ∀ᵐ t ∂(volume : Measure ℝ), ∀ᵐ x ∂((μHE[m] : Measure (Eucl P)).restrict (M ∩ f ⁻¹' {t})), p x) → ∀ᵐ t ∂(volume : Measure ℝ), AEStronglyMeasurable (fun x => (ξ x).comp ((ContinuousAlternatingMap.alternatizeUncurryFinCLM ℝ (Eucl P) ℝ).comp (ContinuousLinearMap.smulRightL ℝ (Eucl P) (Covector (Eucl P) m) (innerSL ℝ (‖G x‖⁻¹ • G x))))) ((μHE[m] : Measure (Eucl P)).restrict (M ∩ f ⁻¹' {t}))`

## Sibling prerequisites

- `root.slicing-a1.slice_integer_multiplicity-a1.slice_triple-a1.measure_fields-a1.contraction_lipschitz-a1`

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
