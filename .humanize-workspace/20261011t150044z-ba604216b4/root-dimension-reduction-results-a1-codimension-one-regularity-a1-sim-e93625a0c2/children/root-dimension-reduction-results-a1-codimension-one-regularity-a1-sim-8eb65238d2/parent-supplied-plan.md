# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.dimension_reduction_results-a1.codimension_one_regularity-a1.simons_regular_cone-a1.hypercone_plane-a1.first_variation-a1.trace_bound-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-dimension-reduction-results-a1-codimension-one-regularity-a1-sim-8eb65238d2/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.dimension_reduction_results-a1.codimension_one_regularity-a1.simons_regular_cone-a1.hypercone_plane-a1.first_variation-a1`
- Child key: `trace_bound`
- Declaration: `Submission.codim1_hcp_fv_trace_comp_abs_le`
- Exact Lean type: `∀ (P : ℕ) (K : Submodule ℝ (Euclid P)) (L : Euclid P →L[ℝ] Euclid P), |LinearMap.trace ℝ (Euclid P) (K.starProjection.toLinearMap ∘ₗ L.toLinearMap)| ≤ (Module.finrank ℝ K : ℝ) * ‖L‖`

## Sibling prerequisites

- `root.minimizing_implies_stationary-a1.first_variation_mass_bound-a1.trace_projection_frame-a1`

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
