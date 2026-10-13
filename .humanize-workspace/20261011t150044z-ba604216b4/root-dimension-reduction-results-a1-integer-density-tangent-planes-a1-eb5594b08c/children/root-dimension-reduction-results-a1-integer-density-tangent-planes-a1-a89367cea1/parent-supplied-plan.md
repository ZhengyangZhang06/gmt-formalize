# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.dimension_reduction_results-a1.integer_density_tangent_planes-a1.flat_point_tangent_plane-a1.blowup_support_slab-a1.dilation_image_slab-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-dimension-reduction-results-a1-integer-density-tangent-planes-a1-a89367cea1/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.dimension_reduction_results-a1.integer_density_tangent_planes-a1.flat_point_tangent_plane-a1.blowup_support_slab-a1`
- Child key: `dilation_image_slab`
- Declaration: `Submission.idtp_tpf_bss_dilation_image_slab`
- Exact Lean type: `∀ (P : ℕ) (S : Set (Euclid P)) (x : Euclid P) (σ β : ℝ), 0 < σ → ∀ (Q : Submodule ℝ (Euclid P)), (∀ y ∈ S, dist y x < σ → ‖(y - x) - Q.starProjection (y - x)‖ < β * σ) → ∀ u ∈ dilation x σ '' S, ‖u‖ < 1 → ‖u - Q.starProjection u‖ < β`

## Sibling prerequisites

- None.

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
