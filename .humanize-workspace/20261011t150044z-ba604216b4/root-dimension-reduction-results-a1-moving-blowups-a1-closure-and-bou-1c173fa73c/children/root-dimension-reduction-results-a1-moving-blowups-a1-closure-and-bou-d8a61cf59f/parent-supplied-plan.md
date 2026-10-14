# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.dimension_reduction_results-a1.moving_blowups-a1.closure_and_boundary_rectifiability-a1.slice_limit-a1.slice_bound-a1.mass_neg-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-dimension-reduction-results-a1-moving-blowups-a1-closure-and-bou-d8a61cf59f/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.dimension_reduction_results-a1.moving_blowups-a1.closure_and_boundary_rectifiability-a1.slice_limit-a1.slice_bound-a1`
- Child key: `mass_neg`
- Declaration: `Submission.dmcbr_sl_sb_massOn_eq_of_apply_eq_neg`
- Exact Lean type: `∀ (P n : ℕ) (U : Set (Euclid P)) (T₁ T₂ : GeometricCurrentOn U n) (W : Set (Euclid P)), (∀ ω : TestFormOn U n, T₁ ω = -T₂ ω) → T₁.massOn W = T₂.massOn W`

## Sibling prerequisites

- None.

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
