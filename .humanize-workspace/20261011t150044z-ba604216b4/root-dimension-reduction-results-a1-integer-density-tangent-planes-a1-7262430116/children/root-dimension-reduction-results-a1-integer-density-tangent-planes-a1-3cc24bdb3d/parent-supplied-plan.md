# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.dimension_reduction_results-a1.integer_density_tangent_planes-a1.cone_constant_density_planar-a1.stationary_cone_sheet_planar-a1.cone_chart-a1.polar_map-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-dimension-reduction-results-a1-integer-density-tangent-planes-a1-3cc24bdb3d/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.dimension_reduction_results-a1.integer_density_tangent_planes-a1.cone_constant_density_planar-a1.stationary_cone_sheet_planar-a1.cone_chart-a1`
- Child key: `polar_map`
- Declaration: `Submission.idtp_ccd_scsp_cc_polar_map`
- Exact Lean type: `∀ (P : ℕ) (u e : Euclid P) (r₀ : ℝ), ‖u‖ = 1 → inner ℝ u e = 0 → 0 < r₀ → ContDiffOn ℝ 1 (fun x : Euclid P => (!₂[‖x‖, Real.arctan (inner ℝ x e / inner ℝ x u)] : Euclid 2)) {x : Euclid P | 0 < inner ℝ x u} ∧ ∀ h : Euclid P, fderiv ℝ (fun x : Euclid P => (!₂[‖x‖, Real.arctan (inner ℝ x e / inner ℝ x u)] : Euclid 2)) (r₀ • u) h = !₂[inner ℝ u h, inner ℝ e h / r₀]`

## Sibling prerequisites

- None.

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
