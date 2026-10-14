# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.dimension_reduction_results-a1.codimension_one_regularity-a1.simons_regular_cone-a1.hypercone_plane-a1.flat_cone_plane-a1.immersion_open-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-dimension-reduction-results-a1-codimension-one-regularity-a1-sim-0a90f63d4e/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.dimension_reduction_results-a1.codimension_one_regularity-a1.simons_regular_cone-a1.hypercone_plane-a1.flat_cone_plane-a1`
- Child key: `immersion_open`
- Declaration: `Submission.codim1_hcp_fcp_immersion_image_open_in_subspace`
- Exact Lean type: `∀ (P m : ℕ) (H : Submodule ℝ (Euclid P)) (B : Set (Euclid m)) (ψ : Euclid m → Euclid P), Module.finrank ℝ H = m → IsOpen B → ContDiffOn ℝ 1 ψ B → (∀ v ∈ B, Injective (fderiv ℝ ψ v)) → ψ '' B ⊆ (H : Set (Euclid P)) → ∃ O : Set (Euclid P), IsOpen O ∧ O ∩ (H : Set (Euclid P)) = ψ '' B`

## Sibling prerequisites

- None.

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
