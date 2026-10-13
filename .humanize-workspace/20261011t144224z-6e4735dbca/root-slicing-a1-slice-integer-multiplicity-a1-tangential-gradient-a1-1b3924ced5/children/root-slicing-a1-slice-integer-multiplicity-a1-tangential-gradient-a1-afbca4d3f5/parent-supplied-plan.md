# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.slicing-a1.slice_integer_multiplicity-a1.tangential_gradient-a1.chart_cover-a1.c1_range_chart_cover-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/nodes/root-slicing-a1-slice-integer-multiplicity-a1-tangential-gradient-a1-afbca4d3f5/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.slicing-a1.slice_integer_multiplicity-a1.tangential_gradient-a1.chart_cover-a1`
- Child key: `c1_range_chart_cover`
- Declaration: `Submission.slicing_im_tg_cc_contDiff_range_chart_cover`
- Exact Lean type: `∀ (n P : ℕ) (G : Eucl n → Eucl P), ContDiff ℝ 1 G → ∃ O : ℕ → Set (Eucl n), (∀ k, IsOpen (O k)) ∧ (∀ k, ∃ K : ℝ≥0, LipschitzOnWith K G (O k)) ∧ (∀ k, ∃ c : ℝ, 0 < c ∧ ∀ w ∈ O k, ∀ w' ∈ O k, c * ‖w - w'‖ ≤ ‖G w - G w'‖) ∧ (μHE[n] : Measure (Eucl P)) (range G \ ⋃ k, G '' O k) = 0`

## Sibling prerequisites

- `root.lipschitz_pushforward_im-a1.lipschitz_c1_immersion_pieces-a1.c1_local_antilipschitz-a1`

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
