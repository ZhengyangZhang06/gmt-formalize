# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.slicing-a1.slice_integer_multiplicity-a1.slice_identity-a1.signed_coarea-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/nodes/root-slicing-a1-slice-integer-multiplicity-a1-slice-identity-a1-signed-coarea-a1/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.slicing-a1.slice_integer_multiplicity-a1.slice_identity-a1`
- Child key: `signed_coarea`
- Declaration: `Submission.slicing_im_si_signed_coarea`
- Exact Lean type: `∀ (P : ℕ) (μ ν : Measure (Eucl P)) (M : Set (Eucl P)) (f : Eucl P → ℝ) (G : Eucl P → Eucl P) (g : Eucl P → ℝ), Measurable f → Measurable G → Measurable g → Integrable (fun x => ‖G x‖ * g x) (μ.restrict M) → (∀ h : Eucl P → ℝ≥0∞, Measurable h → AEMeasurable (fun t : ℝ => ∫⁻ x in M ∩ f ⁻¹' {t}, h x ∂ν) (volume : Measure ℝ) ∧ ∫⁻ t, (∫⁻ x in M ∩ f ⁻¹' {t}, h x ∂ν) ∂(volume : Measure ℝ) = ∫⁻ x in M, ‖G x‖ₑ * h x ∂μ) → Integrable (fun t : ℝ => ∫ x in M ∩ f ⁻¹' {t}, g x ∂ν) (volume : Measure ℝ) ∧ ∀ a b : ℝ, ∫ x in M ∩ f ⁻¹' Ioo a b, ‖G x‖ * g x ∂μ = ∫ t in Ioo a b, (∫ x in M ∩ f ⁻¹' {t}, g x ∂ν)`

## Sibling prerequisites

- None.

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
