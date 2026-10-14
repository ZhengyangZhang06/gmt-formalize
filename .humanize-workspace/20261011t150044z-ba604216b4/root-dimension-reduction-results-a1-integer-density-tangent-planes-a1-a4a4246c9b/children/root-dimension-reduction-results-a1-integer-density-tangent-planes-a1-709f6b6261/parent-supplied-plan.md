# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.dimension_reduction_results-a1.integer_density_tangent_planes-a1.flat_off_null_set-a1.one_dim_cones-a1.ray_orientation-a1.tangent_line-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-dimension-reduction-results-a1-integer-density-tangent-planes-a1-709f6b6261/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.dimension_reduction_results-a1.integer_density_tangent_planes-a1.flat_off_null_set-a1.one_dim_cones-a1.ray_orientation-a1`
- Child key: `tangent_line`
- Declaration: `Submission.idtp_fons_odc_ro_tangent_line`
- Exact Lean type: `∀ (P : ℕ) (M N : Set (Euclid P)) (x v : Euclid P) (δ : ℝ) (Q : Submodule ℝ (Euclid P)), v ≠ 0 → 0 < δ → (μHE[1] : Measure (Euclid P)) N = 0 → M ∩ ball x δ ⊆ range (fun s : ℝ => x + s • v) ∪ N → HasApproximateTangentSpaceAt 1 M x Q → Q = Submodule.span ℝ {v}`

## Sibling prerequisites

- `root.dimension_reduction_results-a1.integer_density_tangent_planes-a1.flat_off_null_set-a1.one_dim_cones-a1.ray_orientation-a1.line_integral_pos-a1`

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
