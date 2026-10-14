# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.dimension_reduction_results-a1.integer_density_tangent_planes-a1.two_dim_cone_density-a1.cone_set_finite_planes-a1.subspace_eq_of_inter_ball-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-dimension-reduction-results-a1-integer-density-tangent-planes-a1-4fbdab790c/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.dimension_reduction_results-a1.integer_density_tangent_planes-a1.two_dim_cone_density-a1.cone_set_finite_planes-a1`
- Child key: `subspace_eq_of_inter_ball`
- Declaration: `Submission.idtp_tdc_csfp_subspace_eq_of_inter_ball`
- Exact Lean type: `∀ (P : ℕ) (Q₁ Q₂ : Submodule ℝ (Euclid P)) (x : Euclid P) (t : ℝ), x ∈ Q₁ → 0 < t → (Q₁ : Set (Euclid P)) ∩ ball x t = (Q₂ : Set (Euclid P)) ∩ ball x t → Q₁ = Q₂`

## Sibling prerequisites

- None.

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
