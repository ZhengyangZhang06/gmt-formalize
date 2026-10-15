# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.dimension_reduction_results-a1.moving_blowups-a1.closure_and_boundary_rectifiability-a1.cycle_im-a1.pointwise-a1.single_plane-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-dimension-reduction-results-a1-moving-blowups-a1-closure-and-bou-b4567f8d4d/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.dimension_reduction_results-a1.moving_blowups-a1.closure_and_boundary_rectifiability-a1.cycle_im-a1.pointwise-a1`
- Child key: `single_plane`
- Declaration: `Submission.dmcbr_ci_pw_single_plane_of_unit_weights`
- Exact Lean type: `∀ (P N : ℕ) (m ν : Measure (Euclid P)) (V : Submodule ℝ (Euclid P)) (w : Fin N → Euclid P) (α : Fin N → ℝ), (∀ i, 1 ≤ α i) → ∑ i, α i ≤ 1 → (∃ i, w i = 0) → ν = ∑ i, ENNReal.ofReal (α i) • m.restrict {y : Euclid P | y - w i ∈ V} → ν = m.restrict (V : Set (Euclid P))`

## Sibling prerequisites

- None.

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
