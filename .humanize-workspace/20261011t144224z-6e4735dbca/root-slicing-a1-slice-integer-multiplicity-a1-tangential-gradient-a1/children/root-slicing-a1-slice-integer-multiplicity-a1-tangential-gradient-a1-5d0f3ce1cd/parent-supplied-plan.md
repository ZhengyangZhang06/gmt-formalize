# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.slicing-a1.slice_integer_multiplicity-a1.tangential_gradient-a1.line_deriv-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/nodes/root-slicing-a1-slice-integer-multiplicity-a1-tangential-gradient-a1-5d0f3ce1cd/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.slicing-a1.slice_integer_multiplicity-a1.tangential_gradient-a1`
- Child key: `line_deriv`
- Declaration: `Submission.slicing_im_tg_line_deriv_of_comp`
- Exact Lean type: `∀ (n P : ℕ) (f : Eucl P → ℝ) (L : ℝ≥0) (Φ : Eucl n → Eucl P) (w : Eucl n), LipschitzWith L f → DifferentiableAt ℝ Φ w → DifferentiableAt ℝ (f ∘ Φ) w → ∀ u : Eucl n, HasDerivAt (fun s : ℝ => f (Φ w + s • fderiv ℝ Φ w u)) (fderiv ℝ (f ∘ Φ) w u) 0`

## Sibling prerequisites

- None.

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
