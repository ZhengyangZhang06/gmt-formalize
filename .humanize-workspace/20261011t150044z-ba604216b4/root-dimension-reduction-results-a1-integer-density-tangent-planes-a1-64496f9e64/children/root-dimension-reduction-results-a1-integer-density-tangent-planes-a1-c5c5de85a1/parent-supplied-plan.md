# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.dimension_reduction_results-a1.integer_density_tangent_planes-a1.cone_sector_endpoint_density-a1.sector_points-a1.density_mult-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-dimension-reduction-results-a1-integer-density-tangent-planes-a1-c5c5de85a1/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.dimension_reduction_results-a1.integer_density_tangent_planes-a1.cone_sector_endpoint_density-a1.sector_points-a1`
- Child key: `density_mult`
- Declaration: `Submission.idtp_cse_sp_density_mult_ae`
- Exact Lean type: `∀ (P n : ℕ) (C : GeometricCurrentOn (univ : Set (Euclid P)) n) (R : IMRep (univ : Set (Euclid P)) n), R.Represents C → ∀ᵐ y ∂(μHE[n] : Measure (Euclid P)), ∀ k : ℕ, 1 ≤ k → HasMassDensity C y k → y ∈ R.carrier ∧ R.mult y = k`

## Sibling prerequisites

- `root.regular_set_dense-a1.mass_eq_weight-a1`
- `root.regular_set_dense-a1.density_eq_multiplicity-a1`
- `root.density_one_implies_regular-a1.epsilon_regularity-a1.allard_graph-a1.support_null-a1.density_comparison-a1`
- `root.density_one_implies_regular-a1.epsilon_regularity-a1.allard_graph-a1.support_null-a1.null_open_nbhd-a1`

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
