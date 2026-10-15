# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.dimension_reduction_results-a1.cone_splitting-a1.split_off_spine-a1.minimality_transfer-a1.competitor_mass-a1.comparison_box-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-dimension-reduction-results-a1-cone-splitting-a1-split-off-spine-02e1b84c90/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.dimension_reduction_results-a1.cone_splitting-a1.split_off_spine-a1.minimality_transfer-a1.competitor_mass-a1`
- Child key: `comparison_box`
- Declaration: `Submission.dimred_cs_sos_mt_cm_comparison_box`
- Exact Lean type: `∀ (P k : ℕ) (g : Fin k → Euclid P) (r s ρ : ℝ), Orthonormal ℝ g → r < s → IsOpen ((Submodule.span ℝ (Set.range g)).starProjection ⁻¹' {x | ∀ i, |inner ℝ (g i) x| < s} ∩ (Submodule.span ℝ (Set.range g))ᗮ.starProjection ⁻¹' ball (0 : Euclid P) ρ) ∧ CompactlyContained ((Submodule.span ℝ (Set.range g)).starProjection ⁻¹' {x | ∀ i, |inner ℝ (g i) x| < s} ∩ (Submodule.span ℝ (Set.range g))ᗮ.starProjection ⁻¹' ball (0 : Euclid P) ρ) univ ∧ ∀ K : Set (Euclid P), K ⊆ ball (0 : Euclid P) ρ → {x | ∀ i, |inner ℝ (g i) x| ≤ r} ∩ (Submodule.span ℝ (Set.range g))ᗮ.starProjection ⁻¹' K ⊆ (Submodule.span ℝ (Set.range g)).starProjection ⁻¹' {x | ∀ i, |inner ℝ (g i) x| < s} ∩ (Submodule.span ℝ (Set.range g))ᗮ.starProjection ⁻¹' ball (0 : Euclid P) ρ`

## Sibling prerequisites

- None.

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
