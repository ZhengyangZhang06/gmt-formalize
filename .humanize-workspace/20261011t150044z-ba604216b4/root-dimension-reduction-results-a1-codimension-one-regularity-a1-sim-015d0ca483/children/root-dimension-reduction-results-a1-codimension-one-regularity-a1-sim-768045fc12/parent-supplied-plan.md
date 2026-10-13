# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.dimension_reduction_results-a1.codimension_one_regularity-a1.simons_regular_cone-a1.hypercone_plane-a1.area_formula-a1.chart_jacobian-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-dimension-reduction-results-a1-codimension-one-regularity-a1-sim-768045fc12/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.dimension_reduction_results-a1.codimension_one_regularity-a1.simons_regular_cone-a1.hypercone_plane-a1.area_formula-a1`
- Child key: `chart_jacobian`
- Declaration: `Submission.codim1_hcp_af_chart_jacobian_factor`
- Exact Lean type: `∀ (P m : ℕ) (M W : Set (Euclid P)) (V : Set (Euclid m)) (ψ : Euclid m → Euclid P) (B : Euclid P →L[ℝ] Euclid P) (v : Euclid m), IsOpen V → IsOpen W → ContDiffOn ℝ 1 ψ V → InjOn ψ V → ψ '' V = W ∩ M → (∀ K ⊆ W, IsCompact K → IsCompact (V ∩ ψ ⁻¹' K)) → (∀ z ∈ V, Injective (fderiv ℝ ψ z)) → v ∈ V → Real.sqrt (Matrix.det (Matrix.of fun k l : Fin m => inner ℝ (B (fderiv ℝ ψ v (EuclideanSpace.single k 1))) (B (fderiv ℝ ψ v (EuclideanSpace.single l 1))))) = Real.sqrt (Matrix.det (Matrix.of fun k l : Fin m => inner ℝ (fderiv ℝ ψ v (EuclideanSpace.single k 1)) (fderiv ℝ ψ v (EuclideanSpace.single l 1)))) * Real.sqrt (((B.comp (Submodule.span ℝ (tangentSpace M (ψ v))).subtypeL).adjoint ∘L (B.comp (Submodule.span ℝ (tangentSpace M (ψ v))).subtypeL)).det)`

## Sibling prerequisites

- `root.minimizing_implies_stationary-a1.chart_tangent_space-a1`
- `root.dimension_reduction_results-a1.codimension_one_regularity-a1.region_density_one-a1.local_unit_rep-a1.area_formula-a1.gram_chain-a1`
- `root.dimension_reduction_results-a1.codimension_one_regularity-a1.simons_regular_cone-a1.hypercone_plane-a1.area_formula-a1.subspace_gram-a1`

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
