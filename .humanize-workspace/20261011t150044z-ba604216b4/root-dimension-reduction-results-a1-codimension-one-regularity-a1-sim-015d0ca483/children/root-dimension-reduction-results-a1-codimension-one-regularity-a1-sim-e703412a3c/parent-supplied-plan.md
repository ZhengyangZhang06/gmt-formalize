# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.dimension_reduction_results-a1.codimension_one_regularity-a1.simons_regular_cone-a1.hypercone_plane-a1.area_formula-a1.chart_area-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-dimension-reduction-results-a1-codimension-one-regularity-a1-sim-e703412a3c/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.dimension_reduction_results-a1.codimension_one_regularity-a1.simons_regular_cone-a1.hypercone_plane-a1.area_formula-a1`
- Child key: `chart_area`
- Declaration: `Submission.codim1_hcp_af_chart_area_formula`
- Exact Lean type: `∀ (P m : ℕ) (M E W : Set (Euclid P)) (V : Set (Euclid m)) (ψ : Euclid m → Euclid P) (Φ : Euclid P → Euclid P), IsOpen V → IsOpen W → ContDiffOn ℝ 1 ψ V → InjOn ψ V → ψ '' V = W ∩ M → (∀ K ⊆ W, IsCompact K → IsCompact (V ∩ ψ ⁻¹' K)) → (∀ z ∈ V, Injective (fderiv ℝ ψ z)) → MeasurableSet E → E ⊆ W ∩ M → ContDiff ℝ 1 Φ → InjOn Φ E → (∀ x ∈ E, Injective (fderiv ℝ Φ x)) → μHE[m] (Φ '' E) = ∫⁻ x in E, ENNReal.ofReal (Real.sqrt ((((fderiv ℝ Φ x).comp (Submodule.span ℝ (tangentSpace M x)).subtypeL).adjoint ∘L ((fderiv ℝ Φ x).comp (Submodule.span ℝ (tangentSpace M x)).subtypeL)).det)) ∂μHE[m]`

## Sibling prerequisites

- `root.dimension_reduction_results-a1.codimension_one_regularity-a1.region_density_one-a1.local_unit_rep-a1.area_formula-a1.gram_area-a1`
- `root.dimension_reduction_results-a1.codimension_one_regularity-a1.simons_regular_cone-a1.hypercone_plane-a1.area_formula-a1.chart_jacobian-a1`

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
