# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.slicing-a1.slice_integer_multiplicity-a1.tangential_gradient-a1.chart_gradient-a1.gram_field-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/nodes/root-slicing-a1-slice-integer-multiplicity-a1-tangential-gradient-a1-c1a07ddeb6/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.slicing-a1.slice_integer_multiplicity-a1.tangential_gradient-a1.chart_gradient-a1`
- Child key: `gram_field`
- Declaration: `Submission.slicing_im_tg_cg_gram_field`
- Exact Lean type: `∀ (P n : ℕ) (Φ : Eucl n → Eucl P) (Ω : Set (Eucl n)) (h : Eucl n → ℝ), IsOpen Ω → ContDiff ℝ 1 Φ → (∀ w ∈ Ω, Function.Injective (fderiv ℝ Φ w)) → ∃ γ : Eucl n → Eucl P, Measurable γ ∧ ∀ w ∈ Ω, γ w ∈ LinearMap.range (fderiv ℝ Φ w).toLinearMap ∧ ∀ u : Eucl n, inner ℝ (γ w) (fderiv ℝ Φ w u) = fderiv ℝ h w u`

## Sibling prerequisites

- None.

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
