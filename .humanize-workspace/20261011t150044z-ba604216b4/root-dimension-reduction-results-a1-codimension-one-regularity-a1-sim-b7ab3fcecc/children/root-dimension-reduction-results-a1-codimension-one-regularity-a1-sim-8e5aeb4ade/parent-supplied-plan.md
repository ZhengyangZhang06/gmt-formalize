# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.dimension_reduction_results-a1.codimension_one_regularity-a1.simons_regular_cone-a1.offvertex_rep-a1.submanifold_local-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-dimension-reduction-results-a1-codimension-one-regularity-a1-sim-8e5aeb4ade/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.dimension_reduction_results-a1.codimension_one_regularity-a1.simons_regular_cone-a1.offvertex_rep-a1`
- Child key: `submanifold_local`
- Declaration: `Submission.codim1_ovr_embedded_submanifold_local`
- Exact Lean type: `∀ (P r d : ℕ) (M : Set (Euclid P)), 1 ≤ r → (∀ y ∈ M, ∃ O : Set (Euclid P), IsOpen O ∧ y ∈ O ∧ IsEmbeddedSubmanifold r d (M ∩ O)) → IsEmbeddedSubmanifold r d M ∧ ∀ O : Set (Euclid P), IsOpen O → IsEmbeddedSubmanifold r d (M ∩ O) ∧ ∀ w ∈ M ∩ O, tangentSpace (M ∩ O) w = tangentSpace M w`

## Sibling prerequisites

- `root.minimizing_implies_stationary-a1.chart_tangent_space-a1`

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
