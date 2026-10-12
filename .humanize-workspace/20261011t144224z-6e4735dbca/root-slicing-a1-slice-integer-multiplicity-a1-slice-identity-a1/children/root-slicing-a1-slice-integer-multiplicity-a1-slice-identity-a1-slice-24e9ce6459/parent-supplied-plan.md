# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.slicing-a1.slice_integer_multiplicity-a1.slice_identity-a1.slice_transfer-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/nodes/root-slicing-a1-slice-integer-multiplicity-a1-slice-identity-a1-slice-24e9ce6459/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.slicing-a1.slice_integer_multiplicity-a1.slice_identity-a1`
- Child key: `slice_transfer`
- Declaration: `Submission.slicing_im_si_slice_ae_transfer`
- Exact Lean type: `∀ (P : ℕ) (μ ν : Measure (Eucl P)) (M S : Set (Eucl P)) (f g F : Eucl P → ℝ), NullMeasurableSet M μ → MeasurableSet S → Measurable f → (∀ Z : Set (Eucl P), Z ⊆ M → μ Z = 0 → ∀ᵐ t ∂(volume : Measure ℝ), ν (Z ∩ f ⁻¹' {t}) = 0) → (∀ x, x ∉ S → g x = 0) → (∀ᵐ x ∂(μ.restrict M), x ∈ S → g x = F x) → ∀ᵐ t ∂(volume : Measure ℝ), ∫ x in M ∩ f ⁻¹' {t}, g x ∂ν = ∫ x in {x | x ∈ M ∧ f x = t ∧ x ∈ S}, F x ∂ν`

## Sibling prerequisites

- None.

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
