# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.dimension_reduction_results-a1.codimension_one_regularity-a1.simons_regular_cone-a1.hypercone_plane-a1.first_variation-a1.tangent_projection-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-dimension-reduction-results-a1-codimension-one-regularity-a1-sim-e889567aa4/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.dimension_reduction_results-a1.codimension_one_regularity-a1.simons_regular_cone-a1.hypercone_plane-a1.first_variation-a1`
- Child key: `tangent_projection`
- Declaration: `Submission.codim1_hcp_fv_tangent_projection_continuousOn`
- Exact Lean type: `∀ (P m : ℕ) (M : Set (Euclid P)), IsEmbeddedSubmanifold 1 m M → (∀ x ∈ M, Module.finrank ℝ (Submodule.span ℝ (tangentSpace M x)) = m) ∧ ContinuousOn (fun x => (Submodule.span ℝ (tangentSpace M x)).starProjection) M ∧ ∀ X : Euclid P → Euclid P, ContDiff ℝ 1 X → ContinuousOn (fun x => LinearMap.trace ℝ (Euclid P) ((Submodule.span ℝ (tangentSpace M x)).starProjection.toLinearMap ∘ₗ (fderiv ℝ X x).toLinearMap)) M`

## Sibling prerequisites

- `root.density_one_implies_regular-a1.mean_curvature_monotonicity-a1.chart_tangent_space-a1`

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
