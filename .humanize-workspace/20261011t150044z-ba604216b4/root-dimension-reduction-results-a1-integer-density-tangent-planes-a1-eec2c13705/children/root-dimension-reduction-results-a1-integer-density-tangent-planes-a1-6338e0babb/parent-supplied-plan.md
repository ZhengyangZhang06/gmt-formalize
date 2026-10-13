# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.dimension_reduction_results-a1.integer_density_tangent_planes-a1.two_dim_cone_density-a1.planes_union_vertex_density-a1.plane_domain-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-dimension-reduction-results-a1-integer-density-tangent-planes-a1-6338e0babb/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.dimension_reduction_results-a1.integer_density_tangent_planes-a1.two_dim_cone_density-a1.planes_union_vertex_density-a1`
- Child key: `plane_domain`
- Declaration: `Submission.idtp_tdc_puvd_plane_domain`
- Exact Lean type: `∀ (P q : ℕ) (Ps : Fin q → Submodule ℝ (Euclid P)) (i : Fin q), Module.finrank ℝ (Ps i) = 2 → (∀ j, j ≠ i → Ps i ⊓ Ps j = ⊥) → ∃ V : Set (Euclid P), IsOpen V ∧ IsConnected (V ∩ (Ps i : Set (Euclid P))) ∧ (Ps i : Set (Euclid P)) \ {0} ⊆ V ∧ ∀ j, j ≠ i → Disjoint V (Ps j : Set (Euclid P))`

## Sibling prerequisites

- None.

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
