# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.slicing-a1.slice_integer_multiplicity-a1.tangential_gradient-a1.chart_cover-a1.lipschitz_range_cover-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/nodes/root-slicing-a1-slice-integer-multiplicity-a1-tangential-gradient-a1-81832218ac/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.slicing-a1.slice_integer_multiplicity-a1.tangential_gradient-a1.chart_cover-a1`
- Child key: `lipschitz_range_cover`
- Declaration: `Submission.slicing_im_tg_cc_lipschitz_range_c1_cover`
- Exact Lean type: `∀ (n P : ℕ) (F : Eucl n → Eucl P) (K : ℝ≥0), LipschitzWith K F → ∃ G : ℕ → Eucl n → Eucl P, (∀ i, ContDiff ℝ 1 (G i)) ∧ (μHE[n] : Measure (Eucl P)) (range F \ ⋃ i, range (G i)) = 0`

## Sibling prerequisites

- `root.lipschitz_pushforward_im-a1.lipschitz_c1_immersion_pieces-a1.c1_approximation_eucl-a1`

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
