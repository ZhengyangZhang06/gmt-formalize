# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.dimension_reduction_results-a1.codimension_one_regularity-a1.simons_regular_cone-a1.hypercone_plane-a1.unit_normal-a1.smooth_glue-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-dimension-reduction-results-a1-codimension-one-regularity-a1-sim-98531a38b5/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.dimension_reduction_results-a1.codimension_one_regularity-a1.simons_regular_cone-a1.hypercone_plane-a1.unit_normal-a1`
- Child key: `smooth_glue`
- Declaration: `Submission.codim1_hcp_un_smooth_glue`
- Exact Lean type: `∀ (P : ℕ) (F : Type) [NormedAddCommGroup F] [NormedSpace ℝ F] (M : Set (Euclid P)) (f : Euclid P → F), (∀ y ∈ M, ∃ (O : Set (Euclid P)) (g : Euclid P → F), IsOpen O ∧ y ∈ O ∧ ContDiffOn ℝ (⊤ : ℕ∞) g O ∧ ∀ z ∈ M ∩ O, g z = f z) → ∃ (ν : Euclid P → F) (O : Set (Euclid P)), IsOpen O ∧ M ⊆ O ∧ ContDiffOn ℝ (⊤ : ℕ∞) ν O ∧ ∀ x ∈ M, ν x = f x`

## Sibling prerequisites

- None.

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
