# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.slicing-a1.slice_integer_multiplicity-a1.coarea-a1.line_deriv-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/nodes/root-slicing-a1-slice-integer-multiplicity-a1-coarea-a1-line-deriv-a1/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.slicing-a1.slice_integer_multiplicity-a1.coarea-a1`
- Child key: `line_deriv`
- Declaration: `Submission.slicing_im_coarea_line_deriv`
- Exact Lean type: `∀ (n P : ℕ) (F : Eucl P → ℝ) (Φ : Eucl n → Eucl P) (w : Eucl n), (∃ K : ℝ≥0, ∃ V ∈ 𝓝 (Φ w), LipschitzOnWith K F V) → DifferentiableAt ℝ Φ w → DifferentiableAt ℝ (F ∘ Φ) w → ∀ s : Eucl n, HasDerivAt (fun t : ℝ => F (Φ w + t • fderiv ℝ Φ w s)) (fderiv ℝ (F ∘ Φ) w s) 0`

## Sibling prerequisites

- None.

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
