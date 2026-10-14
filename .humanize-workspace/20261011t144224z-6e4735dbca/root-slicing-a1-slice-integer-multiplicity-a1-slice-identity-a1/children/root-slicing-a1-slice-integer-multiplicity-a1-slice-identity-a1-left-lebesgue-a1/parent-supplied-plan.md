# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.slicing-a1.slice_integer_multiplicity-a1.slice_identity-a1.left_lebesgue-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/nodes/root-slicing-a1-slice-integer-multiplicity-a1-slice-identity-a1-left-lebesgue-a1/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.slicing-a1.slice_integer_multiplicity-a1.slice_identity-a1`
- Child key: `left_lebesgue`
- Declaration: `Submission.slicing_im_si_left_lebesgue_point`
- Exact Lean type: `∀ φ : ℝ → ℝ, LocallyIntegrable φ (volume : Measure ℝ) → ∀ᵐ t ∂(volume : Measure ℝ), Tendsto (fun ε : ℝ => ε⁻¹ * ∫ r in Ioo (t - ε) t, φ r) (𝓝[>] 0) (𝓝 (φ t))`

## Sibling prerequisites

- None.

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
