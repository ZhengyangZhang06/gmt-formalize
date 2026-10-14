# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.dimension_reduction_results-a1.integer_density_tangent_planes-a1.flat_off_null_set-a1.one_dim_cones-a1.line_param-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-dimension-reduction-results-a1-integer-density-tangent-planes-a1-5390c45117/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.dimension_reduction_results-a1.integer_density_tangent_planes-a1.flat_off_null_set-a1.one_dim_cones-a1`
- Child key: `line_param`
- Declaration: `Submission.idtp_fons_odc_line_hausdorff`
- Exact Lean type: `unitBallVolume 1 = 2 ∧ ∀ (P : ℕ) (p v : Euclid P), ‖v‖ = 1 → MeasurableEmbedding (fun t : ℝ => p + t • v) ∧ ∀ I : Set ℝ, (μHE[1] : Measure (Euclid P)).restrict ((fun t : ℝ => p + t • v) '' I) = Measure.map (fun t : ℝ => p + t • v) (volume.restrict I) ∧ (μHE[1] : Measure (Euclid P)) ((fun t : ℝ => p + t • v) '' I) = volume I`

## Sibling prerequisites

- None.

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
