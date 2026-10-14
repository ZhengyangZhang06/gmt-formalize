# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.dimension_reduction_results-a1.codimension_one_regularity-a1.simons_regular_cone-a1.hypercone_plane-a1.flat_cone_plane-a1.planar_globalize-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-dimension-reduction-results-a1-codimension-one-regularity-a1-sim-407063d934/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.dimension_reduction_results-a1.codimension_one_regularity-a1.simons_regular_cone-a1.hypercone_plane-a1.flat_cone_plane-a1`
- Child key: `planar_globalize`
- Declaration: `Submission.codim1_hcp_fcp_locally_planar_is_plane`
- Exact Lean type: `∀ (P m : ℕ) (A₀ : Submodule ℝ (Euclid P)) (M : Set (Euclid P)), 2 ≤ m → Module.finrank ℝ A₀ = m + 1 → M.Nonempty → (0 : Euclid P) ∉ M → closure M ⊆ insert 0 M → (∀ x ∈ M, ∃ H : Submodule ℝ (Euclid P), Module.finrank ℝ H = m ∧ H ≤ A₀ ∧ ∃ O : Set (Euclid P), IsOpen O ∧ x ∈ O ∧ O ∩ M = O ∩ (H : Set (Euclid P))) → ∃ H₀ : Submodule ℝ (Euclid P), Module.finrank ℝ H₀ = m ∧ M = (H₀ : Set (Euclid P)) \ {0}`

## Sibling prerequisites

- `root.dimension_reduction_results-a1.codimension_one_regularity-a1.simons_regular_cone-a1.hypercone_plane-a1.flat_cone_plane-a1.punctured_connected-a1`

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
