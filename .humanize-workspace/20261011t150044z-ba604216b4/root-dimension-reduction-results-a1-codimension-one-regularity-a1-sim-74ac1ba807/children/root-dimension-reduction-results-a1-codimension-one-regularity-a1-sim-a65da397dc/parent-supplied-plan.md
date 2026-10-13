# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.dimension_reduction_results-a1.codimension_one_regularity-a1.simons_regular_cone-a1.hypercone_plane-a1.stability-a1.normal_variation_algebra-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-dimension-reduction-results-a1-codimension-one-regularity-a1-sim-a65da397dc/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.dimension_reduction_results-a1.codimension_one_regularity-a1.simons_regular_cone-a1.hypercone_plane-a1.stability-a1`
- Child key: `normal_variation_algebra`
- Declaration: `Submission.codim1_hcp_stab_normal_variation_algebra`
- Exact Lean type: `∀ (P : ℕ) (S : Submodule ℝ (Euclid P)) (ν₀ : Euclid P) (N L : Euclid P →L[ℝ] Euclid P) (g : Euclid P →L[ℝ] ℝ) (ζ : ℝ), ‖ν₀‖ = 1 → (∀ v ∈ S, inner ℝ ν₀ v = 0) → (∀ τ ∈ S, N τ ∈ S) → (∀ τ ∈ S, ∀ η ∈ S, inner ℝ η (N τ) = inner ℝ τ (N η)) → (∀ τ ∈ S, L τ = g τ • ν₀ + ζ • N τ) → LinearMap.trace ℝ (Euclid P) (S.starProjection.toLinearMap ∘ₗ L.toLinearMap) = ζ * LinearMap.trace ℝ (Euclid P) (S.starProjection.toLinearMap ∘ₗ N.toLinearMap) ∧ ∑ j : Fin P, (‖L (S.starProjection (EuclideanSpace.single j 1)) - S.starProjection (L (S.starProjection (EuclideanSpace.single j 1)))‖ ^ 2 - inner ℝ (S.starProjection (EuclideanSpace.single j 1)) (L (S.starProjection (L (S.starProjection (EuclideanSpace.single j 1)))))) = ∑ j : Fin P, (g (S.starProjection (EuclideanSpace.single j 1))) ^ 2 - ζ ^ 2 * ∑ j : Fin P, ‖N (S.starProjection (EuclideanSpace.single j 1))‖ ^ 2`

## Sibling prerequisites

- None.

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
