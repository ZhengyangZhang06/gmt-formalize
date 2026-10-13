# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.dimension_reduction_results-a1.codimension_one_regularity-a1.simons_regular_cone-a1.hypercone_plane-a1.smooth_charts-a1.graph_reparam-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-dimension-reduction-results-a1-codimension-one-regularity-a1-sim-3d737a3ccd/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.dimension_reduction_results-a1.codimension_one_regularity-a1.simons_regular_cone-a1.hypercone_plane-a1.smooth_charts-a1`
- Child key: `graph_reparam`
- Declaration: `Submission.codim1_hcp_sc_graph_reparam`
- Exact Lean type: `∀ (P d r : ℕ) (N W : Set (Euclid P)) (V : Set (Euclid d)) (ψ : Euclid d → Euclid P) (π : Euclid P →L[ℝ] Euclid d) (c : Euclid P) (v₀ : Euclid d), 1 ≤ r → IsOpen V → IsOpen W → ContDiffOn ℝ r ψ V → InjOn ψ V → ψ '' V = W ∩ N → (∀ K ⊆ W, IsCompact K → IsCompact (V ∩ ψ ⁻¹' K)) → v₀ ∈ V → Injective (π ∘L fderiv ℝ ψ v₀) → ∃ (D : Set (Euclid d)) (O : Set (Euclid P)) (g : Euclid d → Euclid P), IsOpen D ∧ IsOpen O ∧ ψ v₀ ∈ O ∧ O ⊆ W ∧ ContDiffOn ℝ r g D ∧ InjOn g D ∧ g '' D = O ∩ N ∧ (∀ K ⊆ O, IsCompact K → IsCompact (D ∩ g ⁻¹' K)) ∧ (∀ a ∈ D, Injective (fderiv ℝ g a)) ∧ ∀ a ∈ D, π (g a - c) = a`

## Sibling prerequisites

- `root.density_and_tangent_cones-a1.blowup_compactness-a1.local_retraction-a1.chart_image_nhds-a1`
- `root.dimension_reduction_results-a1.codimension_one_regularity-a1.simons_regular_cone-a1.hypercone_plane-a1.smooth_charts-a1.local_inverse_cr-a1`
- `root.dimension_reduction_results-a1.codimension_one_regularity-a1.simons_regular_cone-a1.hypercone_plane-a1.smooth_charts-a1.left_inverse_immersion-a1`

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
