# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.dimension_reduction_results-a1.codimension_one_regularity-a1.simons_regular_cone-a1.hypercone_plane-a1.stability-a1.jacobian_bound-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-dimension-reduction-results-a1-codimension-one-regularity-a1-sim-9b223af990/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.dimension_reduction_results-a1.codimension_one_regularity-a1.simons_regular_cone-a1.hypercone_plane-a1.stability-a1`
- Child key: `jacobian_bound`
- Declaration: `Submission.codim1_hcp_stab_jacobian_bound`
- Exact Lean type: `∀ (P : ℕ) (Λ : ℝ), ∃ C : ℝ, ∀ (S : Submodule ℝ (Euclid P)) (L : Euclid P →L[ℝ] Euclid P), ‖L‖ ≤ Λ → LinearMap.trace ℝ (Euclid P) (S.starProjection.toLinearMap ∘ₗ L.toLinearMap) = 0 → ∀ t : ℝ, |t| ≤ 1 → Real.sqrt ((((ContinuousLinearMap.id ℝ (Euclid P) + t • L).comp S.subtypeL).adjoint ∘L ((ContinuousLinearMap.id ℝ (Euclid P) + t • L).comp S.subtypeL)).det) ≤ 1 + t ^ 2 / 2 * ∑ j : Fin P, (‖L (S.starProjection (EuclideanSpace.single j 1)) - S.starProjection (L (S.starProjection (EuclideanSpace.single j 1)))‖ ^ 2 - inner ℝ (S.starProjection (EuclideanSpace.single j 1)) (L (S.starProjection (L (S.starProjection (EuclideanSpace.single j 1)))))) + C * |t| ^ 3`

## Sibling prerequisites

- `root.dimension_reduction_results-a1.codimension_one_regularity-a1.simons_regular_cone-a1.hypercone_plane-a1.stability-a1.det_second_order-a1`

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
