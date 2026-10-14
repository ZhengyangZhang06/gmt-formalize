# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.dimension_reduction_results-a1.integer_density_tangent_planes-a1.two_dim_cone_density-a1.density_locally_constant-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-dimension-reduction-results-a1-integer-density-tangent-planes-a1-ca9016021f/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.dimension_reduction_results-a1.integer_density_tangent_planes-a1.two_dim_cone_density-a1`
- Child key: `density_locally_constant`
- Declaration: `Submission.idtp_tdc_density_locally_constant`
- Exact Lean type: `∀ (P : ℕ) (C : GeometricCurrentOn (univ : Set (Euclid P)) 2), IsMinimizingIn C univ → BoundaryVanishes C → IsConeCurrent C → ∀ p ∈ C.support, p ≠ 0 → ∃ (δ : ℝ) (k : ℕ), 0 < δ ∧ ∀ y ∈ C.support, y ∈ ball p δ → HasMassDensity C y k`

## Sibling prerequisites

- `root.dimension_reduction_results-a1.integer_density_tangent_planes-a1.two_dim_cone_density-a1.cone_dilation-a1`
- `root.dimension_reduction_results-a1.integer_density_tangent_planes-a1.two_dim_cone_density-a1.arc_continuation-a1`
- `root.dimension_reduction_results-a1.integer_density_tangent_planes-a1.two_dim_cone_density-a1.no_infinite_planar_pieces-a1`

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
