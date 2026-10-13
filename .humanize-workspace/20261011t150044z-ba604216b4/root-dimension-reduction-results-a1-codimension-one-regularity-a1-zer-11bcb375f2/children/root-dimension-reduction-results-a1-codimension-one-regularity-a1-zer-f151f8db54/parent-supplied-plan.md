# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.dimension_reduction_results-a1.codimension_one_regularity-a1.zero_scale_limit_plane-a1.graph_area-a1.local_comparison-a1.jacobian_continuous_on-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-dimension-reduction-results-a1-codimension-one-regularity-a1-zer-f151f8db54/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.dimension_reduction_results-a1.codimension_one_regularity-a1.zero_scale_limit_plane-a1.graph_area-a1.local_comparison-a1`
- Child key: `jacobian_continuous_on`
- Declaration: `Submission.codim1_zsl_ga_lc_jacobian_continuousOn`
- Exact Lean type: `∀ (m P : ℕ) (F : Euclid m → Euclid P) (D : Set (Euclid m)), IsOpen D → ContDiffOn ℝ 1 F D → ContinuousOn (fun w => Real.sqrt (((fderiv ℝ F w).adjoint ∘L fderiv ℝ F w).det)) D`

## Sibling prerequisites

- None.

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
