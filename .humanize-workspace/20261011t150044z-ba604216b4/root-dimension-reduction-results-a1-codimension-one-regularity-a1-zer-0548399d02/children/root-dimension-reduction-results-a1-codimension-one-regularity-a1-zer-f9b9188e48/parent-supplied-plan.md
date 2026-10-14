# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.dimension_reduction_results-a1.codimension_one_regularity-a1.zero_scale_limit_plane-a1.bv_compactness-a1.translate_continuity-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-dimension-reduction-results-a1-codimension-one-regularity-a1-zer-f9b9188e48/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.dimension_reduction_results-a1.codimension_one_regularity-a1.zero_scale_limit_plane-a1.bv_compactness-a1`
- Child key: `translate_continuity`
- Declaration: `Submission.codim1_zsl_pc_translate_tendsto_zero`
- Exact Lean type: `∀ (m : ℕ) (F : Set (Euclid m)) (R : ℝ), MeasurableSet F → Tendsto (fun z : Euclid m => volume (symmDiff ((fun v => v + z) ⁻¹' F) F ∩ ball (0 : Euclid m) R)) (𝓝 0) (𝓝 0)`

## Sibling prerequisites

- None.

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
