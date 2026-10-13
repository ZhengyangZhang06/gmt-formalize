# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.dimension_reduction_results-a1.codimension_one_regularity-a1.simons_regular_cone-a1.area_comparison-a1.submanifold_approx_tangent-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-dimension-reduction-results-a1-codimension-one-regularity-a1-sim-5d24065c78/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.dimension_reduction_results-a1.codimension_one_regularity-a1.simons_regular_cone-a1.area_comparison-a1`
- Child key: `submanifold_approx_tangent`
- Declaration: `Submission.codim1_ac_submanifold_approxTangent`
- Exact Lean type: `∀ (P m : ℕ) (N W : Set (Euclid P)) (x : Euclid P) (Q : Submodule ℝ (Euclid P)), 1 ≤ m → IsEmbeddedSubmanifold 1 m N → IsOpen W → x ∈ N ∩ W → (Q : Set (Euclid P)) = tangentSpace N x → HasApproximateTangentSpaceAt m (N ∩ W) x Q`

## Sibling prerequisites

- `root.minimizing_implies_stationary-a1.chart_tangent_space-a1`

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
