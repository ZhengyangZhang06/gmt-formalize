# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.dimension_reduction_results-a1.codimension_one_regularity-a1.zero_scale_limit_plane-a1.graph_area-a1.local_comparison-a1.graph_fderiv-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-dimension-reduction-results-a1-codimension-one-regularity-a1-zer-83ff847c4f/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.dimension_reduction_results-a1.codimension_one_regularity-a1.zero_scale_limit_plane-a1.graph_area-a1.local_comparison-a1`
- Child key: `graph_fderiv`
- Declaration: `Submission.codim1_zsl_ga_lc_graph_fderiv`
- Exact Lean type: `∀ (m k : ℕ) (ι : Euclid m →ₗᵢ[ℝ] Euclid (m + k)) (ι' : Euclid k →ₗᵢ[ℝ] Euclid (m + k)) (g : Euclid m → Euclid k) (w₀ : Euclid m), (∀ v w, inner ℝ (ι v) (ι' w) = 0) → DifferentiableAt ℝ g w₀ → fderiv ℝ (fun w => ι w + ι' (g w)) w₀ = ι.toContinuousLinearMap + ι'.toContinuousLinearMap ∘L fderiv ℝ g w₀ ∧ ∀ h : Euclid m, ‖h‖ ≤ ‖fderiv ℝ (fun w => ι w + ι' (g w)) w₀ h‖`

## Sibling prerequisites

- None.

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
