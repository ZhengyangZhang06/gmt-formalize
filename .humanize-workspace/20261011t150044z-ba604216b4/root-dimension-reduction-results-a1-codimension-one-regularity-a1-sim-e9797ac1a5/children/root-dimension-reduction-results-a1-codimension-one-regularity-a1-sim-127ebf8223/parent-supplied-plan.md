# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.dimension_reduction_results-a1.codimension_one_regularity-a1.simons_regular_cone-a1.hypercone_plane-a1.lipschitz_approx-a1.measurability-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-dimension-reduction-results-a1-codimension-one-regularity-a1-sim-127ebf8223/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.dimension_reduction_results-a1.codimension_one_regularity-a1.simons_regular_cone-a1.hypercone_plane-a1.lipschitz_approx-a1`
- Child key: `measurability`
- Declaration: `Submission.codim1_hcp_lsa_tangential_derivative_aesm`
- Exact Lean type: `∀ (P m : ℕ) (M : Set (Euclid P)) (ζ : Euclid P → ℝ), IsEmbeddedSubmanifold 1 m M → LocallyLipschitzOn M ζ → AEStronglyMeasurable (fun x => (fderivWithin ℝ ζ M x).comp (Submodule.span ℝ (tangentSpace M x)).starProjection) (μHE[m].restrict M)`

## Sibling prerequisites

- `root.dimension_reduction_results-a1.codimension_one_regularity-a1.simons_regular_cone-a1.hypercone_plane-a1.lipschitz_approx-a1.graph_chart-a1`
- `root.dimension_reduction_results-a1.codimension_one_regularity-a1.simons_regular_cone-a1.hypercone_plane-a1.lipschitz_approx-a1.projection_continuity-a1`
- `root.dimension_reduction_results-a1.codimension_one_regularity-a1.simons_regular_cone-a1.hypercone_plane-a1.lipschitz_approx-a1.rademacher-a1`
- `root.dimension_reduction_results-a1.regular_point_density-a1.locally_closed-a1`

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
