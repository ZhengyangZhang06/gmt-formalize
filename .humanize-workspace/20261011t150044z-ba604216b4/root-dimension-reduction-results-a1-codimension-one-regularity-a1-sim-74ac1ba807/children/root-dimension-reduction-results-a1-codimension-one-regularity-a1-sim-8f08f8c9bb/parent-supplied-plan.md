# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.dimension_reduction_results-a1.codimension_one_regularity-a1.simons_regular_cone-a1.hypercone_plane-a1.stability-a1.det_second_order-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-dimension-reduction-results-a1-codimension-one-regularity-a1-sim-8f08f8c9bb/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.dimension_reduction_results-a1.codimension_one_regularity-a1.simons_regular_cone-a1.hypercone_plane-a1.stability-a1`
- Child key: `det_second_order`
- Declaration: `Submission.codim1_hcp_stab_det_second_order`
- Exact Lean type: `∀ (N : ℕ) (κ : ℝ), ∃ C : ℝ, ∀ n : ℕ, n ≤ N → ∀ X Y : Matrix (Fin n) (Fin n) ℝ, (∀ i j, |X i j| ≤ κ) → (∀ i j, |Y i j| ≤ κ) → ∀ t : ℝ, |t| ≤ 1 → |(1 + t • X + t ^ 2 • Y).det - (1 + t * X.trace + t ^ 2 * (Y.trace + (X.trace ^ 2 - (X * X).trace) / 2))| ≤ C * |t| ^ 3`

## Sibling prerequisites

- None.

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
