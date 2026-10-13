# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.slicing-a1.slice_integer_multiplicity-a1.slice_triple-a1.chart_data-a1.lipschitz_on_c1_pieces-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/nodes/root-slicing-a1-slice-integer-multiplicity-a1-slice-triple-a1-chart-d-53709af5bc/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.slicing-a1.slice_integer_multiplicity-a1.slice_triple-a1.chart_data-a1`
- Child key: `lipschitz_on_c1_pieces`
- Declaration: `Submission.slicing_im_st_cd_c1_pieces_of_lipschitzOn`
- Exact Lean type: `∀ (n : ℕ) (Ω : Set (Eucl n)) (u : Eucl n → ℝ) (K : ℝ≥0), IsOpen Ω → LipschitzOnWith K u Ω → ∃ (h : ℕ → Eucl n → ℝ) (A : ℕ → Set (Eucl n)), (∀ k, ContDiff ℝ 1 (h k)) ∧ (∀ k, A k ⊆ Ω) ∧ (∀ k, ∀ w ∈ A k, u w = h k w ∧ HasFDerivAt u (fderiv ℝ (h k) w) w) ∧ (volume : Measure (Eucl n)) (Ω \ ⋃ k, A k) = 0`

## Sibling prerequisites

- `root.lipschitz_pushforward_im-a1.lipschitz_c1_immersion_pieces-a1.c1_approximation_real-a1`

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
