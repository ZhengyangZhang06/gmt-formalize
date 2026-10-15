# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.dimension_reduction_results-a1.cone_splitting-a1.split_off_spine-a1.cone_filling_subspace-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-dimension-reduction-results-a1-cone-splitting-a1-split-off-spine-2cc8704e5d/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.dimension_reduction_results-a1.cone_splitting-a1.split_off_spine-a1`
- Child key: `cone_filling_subspace`
- Declaration: `Submission.dimred_cs_sos_cone_filling_in_subspace`
- Exact Lean type: `∀ (P m : ℕ) (X : GeometricCurrentOn (univ : Set (Euclid P)) m) (V : Submodule ℝ (Euclid P)), 0 < m → IsIntegerMultiplicity X → BoundaryVanishes X → IsCompact X.support → X.support ⊆ (V : Set (Euclid P)) → ∃ Y : GeometricCurrentOn (univ : Set (Euclid P)) (m + 1), IsIntegerMultiplicity Y ∧ Y.boundary = X ∧ IsCompact Y.support ∧ Y.support ⊆ (V : Set (Euclid P))`

## Sibling prerequisites

- `root.dimension_reduction_results-a1.cone_splitting-a1.split_off_spine-a1.lipschitz_tangent-a1`
- `root.minimizing_implies_stationary-a1.support_null-a1`

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
