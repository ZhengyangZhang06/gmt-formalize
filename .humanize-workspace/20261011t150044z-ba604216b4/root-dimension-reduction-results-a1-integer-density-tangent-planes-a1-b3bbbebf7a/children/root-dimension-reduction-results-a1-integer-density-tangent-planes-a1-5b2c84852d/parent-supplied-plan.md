# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.dimension_reduction_results-a1.integer_density_tangent_planes-a1.cone_sector_endpoint_density-a1.rotation_conservation-a1.rotation_divergence-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-dimension-reduction-results-a1-integer-density-tangent-planes-a1-5b2c84852d/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.dimension_reduction_results-a1.integer_density_tangent_planes-a1.cone_sector_endpoint_density-a1.rotation_conservation-a1`
- Child key: `rotation_divergence`
- Declaration: `Submission.idtp_cse_rc_rotation_divergence`
- Exact Lean type: `∀ (P n : ℕ) (M : Set (Euclid P)) (a e x : Euclid P) (g : Euclid P → ℝ), DifferentiableAt ℝ g x → tangentialDivergence n M (fun y : Euclid P => g y • (inner ℝ y a • e - inner ℝ y e • a)) x = fderiv ℝ g x ((approxTangentPlane n M x).starProjection (inner ℝ x a • e - inner ℝ x e • a))`

## Sibling prerequisites

- None.

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
