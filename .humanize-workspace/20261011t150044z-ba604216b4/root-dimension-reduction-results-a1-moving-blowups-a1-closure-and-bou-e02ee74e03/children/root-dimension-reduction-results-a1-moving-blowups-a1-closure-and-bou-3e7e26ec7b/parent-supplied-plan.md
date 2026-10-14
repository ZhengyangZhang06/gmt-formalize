# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.dimension_reduction_results-a1.moving_blowups-a1.closure_and_boundary_rectifiability-a1.cycle_im-a1.blowup_limit-a1.compact_sup_bound-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-dimension-reduction-results-a1-moving-blowups-a1-closure-and-bou-3e7e26ec7b/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.dimension_reduction_results-a1.moving_blowups-a1.closure_and_boundary_rectifiability-a1.cycle_im-a1.blowup_limit-a1`
- Child key: `compact_sup_bound`
- Declaration: `Submission.dmcbr_ci_bl_compact_sup_bound`
- Exact Lean type: `∀ (P : ℕ) (ν : ℕ → Measure (Euclid P)), (∀ i, ν i univ < ∞) → (∀ R : ℝ, 0 < R → ∃ B : ℝ≥0∞, B < ∞ ∧ ∀ᶠ i in atTop, ν i (closedBall 0 R) ≤ B) → ∀ K : Set (Euclid P), IsCompact K → ⨆ i, ν i K < ∞`

## Sibling prerequisites

- None.

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
