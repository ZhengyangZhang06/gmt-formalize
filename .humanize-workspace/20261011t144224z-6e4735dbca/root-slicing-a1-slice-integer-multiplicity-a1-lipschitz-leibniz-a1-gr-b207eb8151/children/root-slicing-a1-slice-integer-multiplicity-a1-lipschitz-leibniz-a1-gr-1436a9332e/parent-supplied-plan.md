# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.slicing-a1.slice_integer_multiplicity-a1.lipschitz_leibniz-a1.gradient_weak_star-a1.pairing_bound-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/nodes/root-slicing-a1-slice-integer-multiplicity-a1-lipschitz-leibniz-a1-gr-1436a9332e/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.slicing-a1.slice_integer_multiplicity-a1.lipschitz_leibniz-a1.gradient_weak_star-a1`
- Child key: `pairing_bound`
- Declaration: `Submission.slicing_im_ll_gws_pairing_bound`
- Exact Lean type: `∀ (n : ℕ) (Ω : Set (Eucl n)) (C : ℝ≥0) (f : Eucl n → ℝ), IsOpen Ω → LipschitzOnWith C f Ω → ∀ b b' : Eucl n → Eucl n, IntegrableOn b Ω (volume : Measure (Eucl n)) → IntegrableOn b' Ω (volume : Measure (Eucl n)) → |(∫ w in Ω, fderiv ℝ f w (b w)) - ∫ w in Ω, fderiv ℝ f w (b' w)| ≤ C * ∫ w in Ω, ‖b w - b' w‖`

## Sibling prerequisites

- None.

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
