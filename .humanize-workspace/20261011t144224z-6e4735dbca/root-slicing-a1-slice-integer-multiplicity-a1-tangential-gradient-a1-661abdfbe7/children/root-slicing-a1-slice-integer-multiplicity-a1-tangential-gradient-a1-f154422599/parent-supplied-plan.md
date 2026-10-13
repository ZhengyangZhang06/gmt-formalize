# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.slicing-a1.slice_integer_multiplicity-a1.tangential_gradient-a1.chart_gradient-a1.borel_transfer-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/nodes/root-slicing-a1-slice-integer-multiplicity-a1-tangential-gradient-a1-f154422599/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.slicing-a1.slice_integer_multiplicity-a1.tangential_gradient-a1.chart_gradient-a1`
- Child key: `borel_transfer`
- Declaration: `Submission.slicing_im_tg_cg_borel_transfer`
- Exact Lean type: `∀ (n P Q : ℕ) (Φ : Eucl n → Eucl P) (D : Set (Eucl n)) (γ : Eucl n → Eucl Q), MeasurableSet D → ContinuousOn Φ D → InjOn Φ D → Measurable γ → ∃ g : Eucl P → Eucl Q, Measurable g ∧ (∀ w ∈ D, g (Φ w) = γ w) ∧ ∀ y, y ∉ Φ '' D → g y = 0`

## Sibling prerequisites

- None.

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
