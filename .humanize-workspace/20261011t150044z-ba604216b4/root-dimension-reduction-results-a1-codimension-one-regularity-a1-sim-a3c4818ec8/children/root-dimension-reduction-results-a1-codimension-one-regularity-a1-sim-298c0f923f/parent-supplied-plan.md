# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.dimension_reduction_results-a1.codimension_one_regularity-a1.simons_regular_cone-a1.hypercone_plane-a1.simons_cone-a1.normal_complement-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-dimension-reduction-results-a1-codimension-one-regularity-a1-sim-298c0f923f/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.dimension_reduction_results-a1.codimension_one_regularity-a1.simons_regular_cone-a1.hypercone_plane-a1.simons_cone-a1`
- Child key: `normal_complement`
- Declaration: `Submission.codim1_hcp_sc_tangent_normal_complement`
- Exact Lean type: `∀ (P m : ℕ) (A₀ : Submodule ℝ (Euclid P)) (M : Set (Euclid P)) (ν : Euclid P → Euclid P), Module.finrank ℝ A₀ = m + 1 → M ⊆ (A₀ : Set (Euclid P)) → IsEmbeddedSubmanifold 1 m M → (∀ x ∈ M, ν x ∈ A₀ ∧ ‖ν x‖ = 1 ∧ ∀ v ∈ tangentSpace M x, inner ℝ (ν x) v = 0) → ∀ x ∈ M, tangentSpace M x = {v : Euclid P | v ∈ A₀ ∧ inner ℝ (ν x) v = 0} ∧ ∀ w : Euclid P, (Submodule.span ℝ (tangentSpace M x)).starProjection w = A₀.starProjection w - inner ℝ (ν x) w • ν x`

## Sibling prerequisites

- `root.minimizing_implies_stationary-a1.chart_tangent_space-a1`

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
