# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.dimension_reduction_results-a1.codimension_one_regularity-a1.simons_regular_cone-a1.area_comparison-a1.submanifold_area-a1.jacobian_continuous-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-dimension-reduction-results-a1-codimension-one-regularity-a1-sim-d22f6b1425/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.dimension_reduction_results-a1.codimension_one_regularity-a1.simons_regular_cone-a1.area_comparison-a1.submanifold_area-a1`
- Child key: `jacobian_continuous`
- Declaration: `Submission.codim1_ac_saf_jacobian_continuousOn`
- Exact Lean type: `∀ (P m : ℕ) (N : Set (Euclid P)) (Q : Euclid P → Submodule ℝ (Euclid P)) (Φ : Euclid P → Euclid P), IsEmbeddedSubmanifold 1 m N → (∀ x ∈ N, (Q x : Set (Euclid P)) = tangentSpace N x) → ContDiff ℝ 1 Φ → ContinuousOn (fun x => Real.sqrt (Matrix.det (Matrix.of fun i j : Fin (Module.finrank ℝ (Q x)) => inner ℝ (fderiv ℝ Φ x (stdOrthonormalBasis ℝ (Q x) i)) (fderiv ℝ Φ x (stdOrthonormalBasis ℝ (Q x) j))))) N`

## Sibling prerequisites

- `root.dimension_reduction_results-a1.codimension_one_regularity-a1.simons_regular_cone-a1.area_comparison-a1.submanifold_area-a1.chart_gram_factor-a1`
- `root.density_one_implies_regular-a1.mean_curvature_monotonicity-a1.chart_tangent_space-a1.inverse_continuity-a1`

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
