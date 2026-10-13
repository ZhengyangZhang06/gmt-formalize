# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.dimension_reduction_results-a1.integer_density_tangent_planes-a1.flat_point_tangent_plane-a1.plane_subsequence_limit-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-dimension-reduction-results-a1-integer-density-tangent-planes-a1-05aee7df87/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.dimension_reduction_results-a1.integer_density_tangent_planes-a1.flat_point_tangent_plane-a1`
- Child key: `plane_subsequence_limit`
- Declaration: `Submission.idtp_tpf_plane_subseq_limit`
- Exact Lean type: `∀ (P n : ℕ) (Qs : ℕ → Submodule ℝ (Euclid P)), (∀ j, Module.finrank ℝ (Qs j) = n) → ∃ (js : ℕ → ℕ) (τ : Fin n → Euclid P) (κ : ℕ → ℝ), StrictMono js ∧ Orthonormal ℝ τ ∧ Tendsto κ atTop (𝓝 0) ∧ ∀ (i : ℕ) (u : Euclid P), ‖(Qs (js i)).starProjection u - (Submodule.span ℝ (Set.range τ)).starProjection u‖ ≤ κ i * ‖u‖`

## Sibling prerequisites

- None.

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
