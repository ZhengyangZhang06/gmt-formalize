# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.dimension_reduction_results-a1.codimension_one_regularity-a1.simons_regular_cone-a1.hypercone_plane-a1.unit_normal-a1.hyperplane_projection-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-dimension-reduction-results-a1-codimension-one-regularity-a1-sim-e3435e52ec/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.dimension_reduction_results-a1.codimension_one_regularity-a1.simons_regular_cone-a1.hypercone_plane-a1.unit_normal-a1`
- Child key: `hyperplane_projection`
- Declaration: `Submission.codim1_hcp_un_hyperplane_projection`
- Exact Lean type: `∀ (P m : ℕ) (A₀ Q : Submodule ℝ (Euclid P)) (n : Euclid P), Module.finrank ℝ A₀ = m + 1 → Module.finrank ℝ Q = m → Q ≤ A₀ → n ∈ A₀ → ‖n‖ = 1 → (∀ v ∈ Q, inner ℝ n v = 0) → ∀ w : Euclid P, Q.starProjection w = A₀.starProjection w - inner ℝ n w • n`

## Sibling prerequisites

- None.

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
