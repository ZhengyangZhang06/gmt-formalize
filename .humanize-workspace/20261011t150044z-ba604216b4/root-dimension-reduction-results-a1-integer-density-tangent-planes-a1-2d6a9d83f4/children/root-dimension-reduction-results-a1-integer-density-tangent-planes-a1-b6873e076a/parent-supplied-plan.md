# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.dimension_reduction_results-a1.integer_density_tangent_planes-a1.cone_sector_endpoint_density-a1.fibre_area-a1.polar_jacobian-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-dimension-reduction-results-a1-integer-density-tangent-planes-a1-b6873e076a/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.dimension_reduction_results-a1.integer_density_tangent_planes-a1.cone_sector_endpoint_density-a1.fibre_area-a1`
- Child key: `polar_jacobian`
- Declaration: `Submission.idtp_cse_fa_polar_gram_jacobian`
- Exact Lean type: `∀ (P : ℕ) (Q T : Submodule ℝ (Euclid P)) (a e x : Euclid P), Module.finrank ℝ Q = 2 → a ∈ Q → e ∈ Q → ‖a‖ = 1 → ‖e‖ = 1 → inner ℝ a e = 0 → 0 < inner ℝ x a → Module.finrank ℝ T = 2 → T.starProjection x = x → Real.sqrt (Matrix.det (Matrix.of fun i j : Fin (Module.finrank ℝ T) => (fderiv ℝ (fun y : Euclid P => (‖y‖, Real.arctan (inner ℝ y e / inner ℝ y a))) x (stdOrthonormalBasis ℝ T i)).1 * (fderiv ℝ (fun y : Euclid P => (‖y‖, Real.arctan (inner ℝ y e / inner ℝ y a))) x (stdOrthonormalBasis ℝ T j)).1 + (fderiv ℝ (fun y : Euclid P => (‖y‖, Real.arctan (inner ℝ y e / inner ℝ y a))) x (stdOrthonormalBasis ℝ T i)).2 * (fderiv ℝ (fun y : Euclid P => (‖y‖, Real.arctan (inner ℝ y e / inner ℝ y a))) x (stdOrthonormalBasis ℝ T j)).2)) = ‖T.starProjection (inner ℝ x a • e - inner ℝ x e • a)‖ / ‖Q.starProjection x‖ ^ 2`

## Sibling prerequisites

- None.

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
