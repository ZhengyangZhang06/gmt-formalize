# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.dimension_reduction_results-a1.integer_density_tangent_planes-a1.cone_constant_density_planar-a1.stationary_cone_sheet_planar-a1.cone_area-a1.prod_area-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-dimension-reduction-results-a1-integer-density-tangent-planes-a1-249b48cc1c/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.dimension_reduction_results-a1.integer_density_tangent_planes-a1.cone_constant_density_planar-a1.stationary_cone_sheet_planar-a1.cone_area-a1`
- Child key: `prod_area`
- Declaration: `Submission.idtp_ccd_scsp_ca_prod_area_formula`
- Exact Lean type: `∀ (P : ℕ) (G : ℝ × ℝ → Euclid P) (R : Set (ℝ × ℝ)) (h : Euclid P → ℝ), MeasurableSet R → (∀ q ∈ R, DifferentiableAt ℝ G q) → (∀ q ∈ R, Injective (fderiv ℝ G q)) → InjOn G R → ∫ x in G '' R, h x ∂μHE[2] = ∫ q in R, Real.sqrt (‖fderiv ℝ G q (1, 0)‖ ^ 2 * ‖fderiv ℝ G q (0, 1)‖ ^ 2 - inner ℝ (fderiv ℝ G q (1, 0)) (fderiv ℝ G q (0, 1)) ^ 2) * h (G q)`

## Sibling prerequisites

- `root.dimension_reduction_results-a1.codimension_one_regularity-a1.region_density_one-a1.local_unit_rep-a1.chart_divergence-a1.gram_area_formula-a1`

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
