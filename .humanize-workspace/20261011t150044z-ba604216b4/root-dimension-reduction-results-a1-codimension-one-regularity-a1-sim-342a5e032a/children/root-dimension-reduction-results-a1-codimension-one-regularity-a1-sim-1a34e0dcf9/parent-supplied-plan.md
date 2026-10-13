# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.dimension_reduction_results-a1.codimension_one_regularity-a1.simons_regular_cone-a1.hypercone_plane-a1.unit_normal-a1.normal_local_smooth-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-dimension-reduction-results-a1-codimension-one-regularity-a1-sim-1a34e0dcf9/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.dimension_reduction_results-a1.codimension_one_regularity-a1.simons_regular_cone-a1.hypercone_plane-a1.unit_normal-a1`
- Child key: `normal_local_smooth`
- Declaration: `Submission.codim1_hcp_un_normal_local_smooth`
- Exact Lean type: `∀ (P m : ℕ) (A₀ : Submodule ℝ (Euclid P)) (M : Set (Euclid P)) (ν₀ : Euclid P → Euclid P), Module.finrank ℝ A₀ = m + 1 → M ⊆ (A₀ : Set (Euclid P)) → (∀ y ∈ M, ∃ (V : Set (Euclid m)) (W : Set (Euclid P)) (ψ : Euclid m → Euclid P), IsOpen V ∧ IsOpen W ∧ y ∈ W ∧ ContDiffOn ℝ (⊤ : ℕ∞) ψ V ∧ InjOn ψ V ∧ ψ '' V = W ∩ M ∧ (∀ K ⊆ W, IsCompact K → IsCompact (V ∩ ψ ⁻¹' K)) ∧ ∀ z ∈ V, Injective (fderiv ℝ ψ z)) → ContinuousOn ν₀ M → (∀ x ∈ M, ν₀ x ∈ A₀ ∧ ‖ν₀ x‖ = 1 ∧ ∀ v ∈ tangentSpace M x, inner ℝ (ν₀ x) v = 0) → ∀ y ∈ M, ∃ (O : Set (Euclid P)) (g : Euclid P → Euclid P), IsOpen O ∧ y ∈ O ∧ ContDiffOn ℝ (⊤ : ℕ∞) g O ∧ ∀ z ∈ M ∩ O, g z = ν₀ z`

## Sibling prerequisites

- `root.minimizing_implies_stationary-a1.chart_tangent_space-a1`
- `root.dimension_reduction_results-a1.codimension_one_regularity-a1.simons_regular_cone-a1.hypercone_plane-a1.unit_normal-a1.tangent_subspace-a1`
- `root.dimension_reduction_results-a1.codimension_one_regularity-a1.simons_regular_cone-a1.hypercone_plane-a1.unit_normal-a1.cross_product-a1`
- `root.dimension_reduction_results-a1.codimension_one_regularity-a1.simons_regular_cone-a1.hypercone_plane-a1.unit_normal-a1.chart_retraction-a1`
- `root.dimension_reduction_results-a1.codimension_one_regularity-a1.simons_regular_cone-a1.hypercone_plane-a1.unit_normal-a1.hyperplane_projection-a1`

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
