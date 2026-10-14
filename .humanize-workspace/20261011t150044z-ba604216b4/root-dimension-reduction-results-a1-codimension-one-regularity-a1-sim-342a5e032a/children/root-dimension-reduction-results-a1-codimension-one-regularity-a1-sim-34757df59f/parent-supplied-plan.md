# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.dimension_reduction_results-a1.codimension_one_regularity-a1.simons_regular_cone-a1.hypercone_plane-a1.unit_normal-a1.orientation_normal-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-dimension-reduction-results-a1-codimension-one-regularity-a1-sim-34757df59f/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.dimension_reduction_results-a1.codimension_one_regularity-a1.simons_regular_cone-a1.hypercone_plane-a1.unit_normal-a1`
- Child key: `orientation_normal`
- Declaration: `Submission.codim1_hcp_un_orientation_normal`
- Exact Lean type: `∀ (P m : ℕ) (A₀ : Submodule ℝ (Euclid P)) (M : Set (Euclid P)) (ξ : Euclid P → MultiVector P m), Module.finrank ℝ A₀ = m + 1 → (∀ x ∈ M, tangentSpace M x ⊆ (A₀ : Set (Euclid P))) → IsOrientation m M ξ → ∃ ν₀ : Euclid P → Euclid P, ContinuousOn ν₀ M ∧ ∀ x ∈ M, ν₀ x ∈ A₀ ∧ ‖ν₀ x‖ = 1 ∧ ∀ v ∈ tangentSpace M x, inner ℝ (ν₀ x) v = 0`

## Sibling prerequisites

- `root.dimension_reduction_results-a1.codimension_one_regularity-a1.simons_regular_cone-a1.hypercone_plane-a1.unit_normal-a1.cross_product-a1`

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
