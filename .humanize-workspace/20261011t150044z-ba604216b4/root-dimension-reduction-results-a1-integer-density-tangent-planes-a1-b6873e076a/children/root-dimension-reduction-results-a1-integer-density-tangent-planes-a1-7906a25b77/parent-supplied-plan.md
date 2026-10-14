# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.dimension_reduction_results-a1.integer_density_tangent_planes-a1.cone_sector_endpoint_density-a1.fibre_area-a1.polar_jacobian-a1.gram_det_two_plane-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-dimension-reduction-results-a1-integer-density-tangent-planes-a1-7906a25b77/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.dimension_reduction_results-a1.integer_density_tangent_planes-a1.cone_sector_endpoint_density-a1.fibre_area-a1.polar_jacobian-a1`
- Child key: `gram_det_two_plane`
- Declaration: `Submission.idtp_cse_fa_pj_gram_det_two_plane`
- Exact Lean type: `∀ (P : ℕ) (T : Submodule ℝ (Euclid P)) (p q : Euclid P), Module.finrank ℝ T = 2 → Matrix.det (Matrix.of fun i j : Fin (Module.finrank ℝ T) => inner ℝ p (stdOrthonormalBasis ℝ T i : Euclid P) * inner ℝ p (stdOrthonormalBasis ℝ T j : Euclid P) + inner ℝ q (stdOrthonormalBasis ℝ T i : Euclid P) * inner ℝ q (stdOrthonormalBasis ℝ T j : Euclid P)) = ‖T.starProjection p‖ ^ 2 * ‖T.starProjection q‖ ^ 2 - inner ℝ (T.starProjection p) (T.starProjection q) ^ 2`

## Sibling prerequisites

- None.

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
