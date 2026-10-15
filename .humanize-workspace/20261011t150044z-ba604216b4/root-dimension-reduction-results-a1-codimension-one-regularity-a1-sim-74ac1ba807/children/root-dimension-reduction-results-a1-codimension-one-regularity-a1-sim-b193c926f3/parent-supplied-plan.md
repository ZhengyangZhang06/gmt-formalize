# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.dimension_reduction_results-a1.codimension_one_regularity-a1.simons_regular_cone-a1.hypercone_plane-a1.stability-a1.variation_field-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-dimension-reduction-results-a1-codimension-one-regularity-a1-sim-b193c926f3/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.dimension_reduction_results-a1.codimension_one_regularity-a1.simons_regular_cone-a1.hypercone_plane-a1.stability-a1`
- Child key: `variation_field`
- Declaration: `Submission.codim1_hcp_stab_variation_field`
- Exact Lean type: `∀ (P : ℕ) (U O M C : Set (Euclid P)) (ν : Euclid P → Euclid P) (ζ : Euclid P → ℝ), IsOpen U → IsOpen O → M ⊆ U → M ⊆ O → ContDiffOn ℝ (⊤ : ℕ∞) ν O → (∀ x ∈ M, ‖ν x‖ = 1) → ContDiff ℝ (⊤ : ℕ∞) ζ → IsCompact C → C ⊆ M → (∀ x ∈ M, x ∉ C → ζ x = 0) → ∃ Z : Euclid P → Euclid P, ContDiff ℝ (⊤ : ℕ∞) Z ∧ HasCompactSupport Z ∧ tsupport Z ⊆ U ∧ (∀ x ∈ M, Z x = ζ x • ν x) ∧ (∀ x ∈ M, ∀ τ ∈ Submodule.span ℝ (tangentSpace M x), fderiv ℝ Z x τ = fderiv ℝ ζ x τ • ν x + ζ x • fderiv ℝ ν x τ) ∧ (∀ x ∈ M, x ∉ tsupport Z → ζ x = 0 ∧ ∀ τ ∈ Submodule.span ℝ (tangentSpace M x), fderiv ℝ ζ x τ = 0)`

## Sibling prerequisites

- None.

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
