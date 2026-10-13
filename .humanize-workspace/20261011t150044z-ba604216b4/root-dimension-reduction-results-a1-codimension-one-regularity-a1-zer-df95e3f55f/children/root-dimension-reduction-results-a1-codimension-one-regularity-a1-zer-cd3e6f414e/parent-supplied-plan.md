# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.dimension_reduction_results-a1.codimension_one_regularity-a1.zero_scale_limit_plane-a1.graph_area-a1.set_identity-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-dimension-reduction-results-a1-codimension-one-regularity-a1-zer-cd3e6f414e/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.dimension_reduction_results-a1.codimension_one_regularity-a1.zero_scale_limit_plane-a1.graph_area-a1`
- Child key: `set_identity`
- Declaration: `Submission.codim1_zsl_ga_set_identity`
- Exact Lean type: `∀ (m k : ℕ) (ι : Euclid m →ₗᵢ[ℝ] Euclid (m + k)) (ι' : Euclid k →ₗᵢ[ℝ] Euclid (m + k)) (g : Euclid m → Euclid k) (D A : Set (Euclid m)), (∀ v w, inner ℝ (ι v) (ι' w) = 0) → IsOpen D → ContDiffOn ℝ 1 g D → MeasurableSet A → A ⊆ D → μHE[m] ((fun w => ι w + ι' (g w)) '' A) = ∫⁻ w in A, ENNReal.ofReal (Real.sqrt (((fderiv ℝ (fun w => ι w + ι' (g w)) w).adjoint ∘L fderiv ℝ (fun w => ι w + ι' (g w)) w).det))`

## Sibling prerequisites

- `root.dimension_reduction_results-a1.codimension_one_regularity-a1.zero_scale_limit_plane-a1.graph_area-a1.local_comparison-a1`

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
