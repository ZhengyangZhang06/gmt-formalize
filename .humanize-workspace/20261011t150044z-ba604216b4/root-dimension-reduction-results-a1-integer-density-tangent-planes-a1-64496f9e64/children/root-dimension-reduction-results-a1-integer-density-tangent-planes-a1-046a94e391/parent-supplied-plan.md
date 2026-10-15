# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.dimension_reduction_results-a1.integer_density_tangent_planes-a1.cone_sector_endpoint_density-a1.sector_points-a1.polar_null-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-dimension-reduction-results-a1-integer-density-tangent-planes-a1-046a94e391/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.dimension_reduction_results-a1.integer_density_tangent_planes-a1.cone_sector_endpoint_density-a1.sector_points-a1`
- Child key: `polar_null`
- Declaration: `Submission.idtp_cse_sp_polar_null_preimage`
- Exact Lean type: `∀ (P : ℕ) (a e : Euclid P) (N : Set (Euclid P)), ‖a‖ = 1 → ‖e‖ = 1 → inner ℝ a e = 0 → μHE[2] N = 0 → ∀ᵐ p : ℝ × ℝ, 0 < p.1 → -Real.pi < p.2 → p.2 < Real.pi → p.1 • (Real.cos p.2 • a + Real.sin p.2 • e) ∉ N`

## Sibling prerequisites

- None.

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
