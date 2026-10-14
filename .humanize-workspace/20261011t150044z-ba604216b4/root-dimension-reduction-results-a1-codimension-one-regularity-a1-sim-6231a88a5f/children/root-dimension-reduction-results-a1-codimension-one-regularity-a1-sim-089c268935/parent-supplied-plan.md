# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.dimension_reduction_results-a1.codimension_one_regularity-a1.simons_regular_cone-a1.hypercone_plane-a1.smooth_charts-a1.graph_regularity-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-dimension-reduction-results-a1-codimension-one-regularity-a1-sim-089c268935/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.dimension_reduction_results-a1.codimension_one_regularity-a1.simons_regular_cone-a1.hypercone_plane-a1.smooth_charts-a1`
- Child key: `graph_regularity`
- Declaration: `Submission.codim1_hcp_sc_graph_contDiffOn`
- Exact Lean type: `∀ (P d r : ℕ) (M W₀ : Set (Euclid P)) (D : Set (Euclid d)) (G : Euclid d → Euclid P) (π : Euclid P →L[ℝ] Euclid d) (c : Euclid P), 1 ≤ r → IsEmbeddedSubmanifold r d M → IsOpen D → IsOpen W₀ → ContDiffOn ℝ 1 G D → InjOn G D → G '' D = W₀ ∩ M → (∀ K ⊆ W₀, IsCompact K → IsCompact (D ∩ G ⁻¹' K)) → (∀ a ∈ D, Injective (fderiv ℝ G a)) → (∀ a ∈ D, π (G a - c) = a) → ContDiffOn ℝ r G D`

## Sibling prerequisites

- `root.minimizing_implies_stationary-a1.chart_tangent_space-a1`
- `root.dimension_reduction_results-a1.codimension_one_regularity-a1.simons_regular_cone-a1.hypercone_plane-a1.smooth_charts-a1.left_inverse_immersion-a1`
- `root.dimension_reduction_results-a1.codimension_one_regularity-a1.simons_regular_cone-a1.hypercone_plane-a1.smooth_charts-a1.graph_reparam-a1`

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
