# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.dimension_reduction_results-a1.integer_density_tangent_planes-a1.cone_constant_density_planar-a1.stationary_cone_sheet_planar-a1.test_field-a1.profile_deriv-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-dimension-reduction-results-a1-integer-density-tangent-planes-a1-96d2d2b97c/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.dimension_reduction_results-a1.integer_density_tangent_planes-a1.cone_constant_density_planar-a1.stationary_cone_sheet_planar-a1.test_field-a1`
- Child key: `profile_deriv`
- Declaration: `Submission.idtp_ccd_scsp_tf_profile_deriv`
- Exact Lean type: `∀ (P : ℕ) (u e x : Euclid P) (φ lam : ℝ → ℝ), ContDiff ℝ 1 φ → ContDiff ℝ 1 lam → 0 < inner ℝ x u → ContDiffAt ℝ 1 (fun y : Euclid P => φ (Real.arctan (inner ℝ y e / inner ℝ y u)) * lam ‖y‖) x ∧ ∀ h : Euclid P, inner ℝ x h = 0 → fderiv ℝ (fun y : Euclid P => φ (Real.arctan (inner ℝ y e / inner ℝ y u)) * lam ‖y‖) x h = deriv φ (Real.arctan (inner ℝ x e / inner ℝ x u)) * lam ‖x‖ * ((inner ℝ x u * inner ℝ h e - inner ℝ x e * inner ℝ h u) / (inner ℝ x u ^ 2 + inner ℝ x e ^ 2))`

## Sibling prerequisites

- None.

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
