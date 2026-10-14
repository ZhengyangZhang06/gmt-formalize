# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.dimension_reduction_results-a1.integer_density_tangent_planes-a1.cone_constant_density_planar-a1.stationary_cone_sheet_planar-a1.test_field-a1.cutoff-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-dimension-reduction-results-a1-integer-density-tangent-planes-a1-f8bd6c6440/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.dimension_reduction_results-a1.integer_density_tangent_planes-a1.cone_constant_density_planar-a1.stationary_cone_sheet_planar-a1.test_field-a1`
- Child key: `cutoff`
- Declaration: `Submission.idtp_ccd_scsp_tf_cutoff`
- Exact Lean type: `∀ (P : ℕ) (K N : Set (Euclid P)), IsCompact K → IsOpen N → K ⊆ N → ∃ ζ : Euclid P → ℝ, ContDiff ℝ 1 ζ ∧ HasCompactSupport ζ ∧ tsupport ζ ⊆ N ∧ ∃ V : Set (Euclid P), IsOpen V ∧ K ⊆ V ∧ ∀ y ∈ V, ζ y = 1`

## Sibling prerequisites

- None.

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
