# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.dimension_reduction_results-a1.codimension_one_regularity-a1.simons_regular_cone-a1.area_comparison-a1.submanifold_area-a1.chart_gram_factor-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-dimension-reduction-results-a1-codimension-one-regularity-a1-sim-208ac2020f/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.dimension_reduction_results-a1.codimension_one_regularity-a1.simons_regular_cone-a1.area_comparison-a1.submanifold_area-a1`
- Child key: `chart_gram_factor`
- Declaration: `Submission.codim1_ac_saf_chart_gram_factor`
- Exact Lean type: `∀ (P m r : ℕ) (N W : Set (Euclid P)) (V : Set (Euclid m)) (ψ : Euclid m → Euclid P) (Q : Euclid P → Submodule ℝ (Euclid P)) (Φ : Euclid P → Euclid P) (v : Euclid m), 1 ≤ r → IsOpen V → IsOpen W → ContDiffOn ℝ r ψ V → InjOn ψ V → ψ '' V = W ∩ N → (∀ K ⊆ W, IsCompact K → IsCompact (V ∩ ψ ⁻¹' K)) → (∀ z ∈ V, Injective (fderiv ℝ ψ z)) → (∀ x ∈ N, (Q x : Set (Euclid P)) = tangentSpace N x) → DifferentiableAt ℝ Φ (ψ v) → v ∈ V → 0 < Matrix.det (Matrix.of fun k l : Fin m => inner ℝ (fderiv ℝ ψ v (EuclideanSpace.single k 1)) (fderiv ℝ ψ v (EuclideanSpace.single l 1))) ∧ Real.sqrt (Matrix.det (Matrix.of fun k l : Fin m => inner ℝ (fderiv ℝ (Φ ∘ ψ) v (EuclideanSpace.single k 1)) (fderiv ℝ (Φ ∘ ψ) v (EuclideanSpace.single l 1)))) = Real.sqrt (Matrix.det (Matrix.of fun i j : Fin (Module.finrank ℝ (Q (ψ v))) => inner ℝ (fderiv ℝ Φ (ψ v) (stdOrthonormalBasis ℝ (Q (ψ v)) i)) (fderiv ℝ Φ (ψ v) (stdOrthonormalBasis ℝ (Q (ψ v)) j)))) * Real.sqrt (Matrix.det (Matrix.of fun k l : Fin m => inner ℝ (fderiv ℝ ψ v (EuclideanSpace.single k 1)) (fderiv ℝ ψ v (EuclideanSpace.single l 1))))`

## Sibling prerequisites

- `root.minimizing_implies_stationary-a1.chart_tangent_space-a1`
- `root.dimension_reduction_results-a1.codimension_one_regularity-a1.region_density_one-a1.local_unit_rep-a1.area_formula-a1.gram_chain-a1`
- `root.minimizing_implies_stationary-a1.diffeo_pushforward-a1.orientation_pushforward-a1.gram_basis_invariance-a1`

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
