# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.dimension_reduction_results-a1.integer_density_tangent_planes-a1.cone_sector_endpoint_density-a1.sector_points-a1.flat_region-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-dimension-reduction-results-a1-integer-density-tangent-planes-a1-7b45d6c222/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.dimension_reduction_results-a1.integer_density_tangent_planes-a1.cone_sector_endpoint_density-a1.sector_points-a1`
- Child key: `flat_region`
- Declaration: `Submission.idtp_cse_sp_flat_region_ae`
- Exact Lean type: `∀ (P n : ℕ) (C : GeometricCurrentOn (univ : Set (Euclid P)) n) (Q : Submodule ℝ (Euclid P)) (G : Set (Euclid P)) (k : ℕ) (R : IMRep (univ : Set (Euclid P)) n), Module.finrank ℝ Q = n → 1 ≤ k → (∀ y ∈ G, y ∈ Q ∧ HasMassDensity C y k ∧ ∃ r : ℝ, 0 < r ∧ (Q : Set (Euclid P)) ∩ ball y r ⊆ G ∧ C.support ∩ ball y r ⊆ (Q : Set (Euclid P))) → R.Represents C → ∀ᵐ y ∂(μHE[n] : Measure (Euclid P)), y ∈ G → y ∈ R.carrier ∧ R.mult y = k ∧ approxTangentPlane n R.carrier y = Q`

## Sibling prerequisites

- `root.dimension_reduction_results-a1.integer_density_tangent_planes-a1.cone_sector_endpoint_density-a1.sector_points-a1.density_mult-a1`
- `root.minimizing_implies_stationary-a1.support_null-a1`
- `root.density_and_tangent_cones-a1.localize-a1.approx_tangent_local-a1`

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
