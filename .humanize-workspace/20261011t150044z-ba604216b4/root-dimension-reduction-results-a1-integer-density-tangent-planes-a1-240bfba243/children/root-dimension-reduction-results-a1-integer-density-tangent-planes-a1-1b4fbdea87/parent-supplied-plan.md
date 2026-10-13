# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.dimension_reduction_results-a1.integer_density_tangent_planes-a1.cone_sector_endpoint_density-a1.box_mass_limits-a1.box_inclusions-a1.arctan_quotient-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-dimension-reduction-results-a1-integer-density-tangent-planes-a1-1b4fbdea87/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.dimension_reduction_results-a1.integer_density_tangent_planes-a1.cone_sector_endpoint_density-a1.box_mass_limits-a1.box_inclusions-a1`
- Child key: `arctan_quotient`
- Declaration: `Submission.idtp_cse_bml_rbi_arctan_quotient_estimate`
- Exact Lean type: `∀ (p q s' : ℝ), 0 < s' → 20 * s' < 1 → |p| ≤ 3 * s' → |q| ≤ 3 * s' → |Real.arctan (q / (1 + p)) - q| ≤ 30 * s' ^ 2`

## Sibling prerequisites

- `root.dimension_reduction_results-a1.integer_density_tangent_planes-a1.cone_sector_endpoint_density-a1.box_mass_limits-a1.box_inclusions-a1.abs_arctan_sub_self-a1`

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
