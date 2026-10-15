# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.dimension_reduction_results-a1.integer_density_tangent_planes-a1.two_dim_cone_density-a1.planes_union_vertex_density-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-dimension-reduction-results-a1-integer-density-tangent-planes-a1-eec2c13705/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.dimension_reduction_results-a1.integer_density_tangent_planes-a1.two_dim_cone_density-a1`
- Child key: `planes_union_vertex_density`
- Declaration: `Submission.idtp_tdc_planes_union_vertex_density`
- Exact Lean type: `∀ (P q : ℕ) (C : GeometricCurrentOn (univ : Set (Euclid P)) 2) (Ps : Fin q → Submodule ℝ (Euclid P)), IsIntegerMultiplicity C → BoundaryVanishes C → (∀ i, Module.finrank ℝ (Ps i) = 2) → (∀ i j, i ≠ j → Ps i ⊓ Ps j = ⊥) → (∀ x ∈ C.support, x ≠ 0 → ∃ i, x ∈ Ps i) → ∃ m : ℕ, HasMassDensity C 0 m`

## Sibling prerequisites

- `root.dimension_reduction_results-a1.integer_density_tangent_planes-a1.two_dim_cone_density-a1.subspace_ball_measure-a1`

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
