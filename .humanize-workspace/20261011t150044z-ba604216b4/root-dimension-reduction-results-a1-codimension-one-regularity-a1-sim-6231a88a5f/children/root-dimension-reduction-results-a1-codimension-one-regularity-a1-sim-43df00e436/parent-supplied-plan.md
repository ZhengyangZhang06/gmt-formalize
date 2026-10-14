# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.dimension_reduction_results-a1.codimension_one_regularity-a1.simons_regular_cone-a1.hypercone_plane-a1.smooth_charts-a1.left_inverse_immersion-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-dimension-reduction-results-a1-codimension-one-regularity-a1-sim-43df00e436/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.dimension_reduction_results-a1.codimension_one_regularity-a1.simons_regular_cone-a1.hypercone_plane-a1.smooth_charts-a1`
- Child key: `left_inverse_immersion`
- Declaration: `Submission.codim1_hcp_sc_left_inverse_immersion`
- Exact Lean type: `∀ (P d : ℕ) (D : Set (Euclid d)) (g : Euclid d → Euclid P) (π : Euclid P →L[ℝ] Euclid d) (c : Euclid P), IsOpen D → DifferentiableOn ℝ g D → (∀ a ∈ D, π (g a - c) = a) → InjOn g D ∧ ∀ a ∈ D, π ∘L fderiv ℝ g a = ContinuousLinearMap.id ℝ (Euclid d) ∧ Injective (fderiv ℝ g a)`

## Sibling prerequisites

- None.

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
