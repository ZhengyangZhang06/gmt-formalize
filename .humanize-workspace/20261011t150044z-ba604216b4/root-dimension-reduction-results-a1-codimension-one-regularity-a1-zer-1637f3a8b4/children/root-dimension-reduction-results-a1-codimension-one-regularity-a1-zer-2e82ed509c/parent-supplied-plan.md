# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.dimension_reduction_results-a1.codimension_one_regularity-a1.zero_scale_limit_plane-a1.flat_limit-a1.isometric_transport-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-dimension-reduction-results-a1-codimension-one-regularity-a1-zer-2e82ed509c/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.dimension_reduction_results-a1.codimension_one_regularity-a1.zero_scale_limit_plane-a1.flat_limit-a1`
- Child key: `isometric_transport`
- Declaration: `Submission.codim1_zsl_fl_isometry_image_setIntegral`
- Exact Lean type: `∀ (m P : ℕ) (ι : Euclid m →ₗᵢ[ℝ] Euclid P) (c : Euclid P) (A : Set (Euclid m)), MeasurableSet A → MeasurableSet ((fun w => ι w + c) '' A) ∧ ∀ f : Euclid P → ℝ, ∫ y in (fun w => ι w + c) '' A, f y ∂μHE[m] = ∫ w in A, f (ι w + c)`

## Sibling prerequisites

- None.

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
