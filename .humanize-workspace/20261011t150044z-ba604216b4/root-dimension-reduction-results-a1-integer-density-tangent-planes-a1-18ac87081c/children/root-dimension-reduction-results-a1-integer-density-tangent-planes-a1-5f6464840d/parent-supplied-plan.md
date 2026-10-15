# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.dimension_reduction_results-a1.integer_density_tangent_planes-a1.cone_sector_endpoint_density-a1.tangent_scaling-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-dimension-reduction-results-a1-integer-density-tangent-planes-a1-5f6464840d/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.dimension_reduction_results-a1.integer_density_tangent_planes-a1.cone_sector_endpoint_density-a1`
- Child key: `tangent_scaling`
- Declaration: `Submission.idtp_cse_cone_approxTangent_smul`
- Exact Lean type: `∀ (P n : ℕ) (C : GeometricCurrentOn (univ : Set (Euclid P)) n) (R : IMRep (univ : Set (Euclid P)) n), IsConeCurrent C → R.Represents C → ∀ r : ℝ, 0 < r → ∀ᵐ x ∂R.measure, approxTangentPlane n R.carrier (r • x) = approxTangentPlane n R.carrier x`

## Sibling prerequisites

- None.

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
