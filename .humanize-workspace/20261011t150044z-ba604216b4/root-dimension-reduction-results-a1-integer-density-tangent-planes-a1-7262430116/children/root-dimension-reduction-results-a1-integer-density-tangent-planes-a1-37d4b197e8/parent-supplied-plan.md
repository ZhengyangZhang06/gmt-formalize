# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.dimension_reduction_results-a1.integer_density_tangent_planes-a1.cone_constant_density_planar-a1.stationary_cone_sheet_planar-a1.cone_chart-a1.scaled_curve_range-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-dimension-reduction-results-a1-integer-density-tangent-planes-a1-37d4b197e8/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.dimension_reduction_results-a1.integer_density_tangent_planes-a1.cone_constant_density_planar-a1.stationary_cone_sheet_planar-a1.cone_chart-a1`
- Child key: `scaled_curve_range`
- Declaration: `Submission.idtp_ccd_scsp_cc_scaled_curve_range`
- Exact Lean type: `∀ (P : ℕ) (γ : ℝ → Euclid P) (G : Euclid 2 → Euclid P) (S : Set (Euclid 2)) (t α : ℝ), IsOpen S → !₂[t, α] ∈ S → (∀ w ∈ S, G w = w 0 • γ (w 1)) → DifferentiableAt ℝ γ α → t ≠ 0 → Set.range (fderiv ℝ G !₂[t, α]) = (Submodule.span ℝ {γ α, deriv γ α} : Set (Euclid P))`

## Sibling prerequisites

- None.

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
