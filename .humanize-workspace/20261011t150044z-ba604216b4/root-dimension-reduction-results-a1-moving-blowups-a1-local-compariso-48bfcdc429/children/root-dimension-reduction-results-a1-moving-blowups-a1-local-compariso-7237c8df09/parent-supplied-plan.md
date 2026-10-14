# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.dimension_reduction_results-a1.moving_blowups-a1.local_comparison-a1.retraction_comparison-a1.measure_subadditive-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-dimension-reduction-results-a1-moving-blowups-a1-local-compariso-7237c8df09/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.dimension_reduction_results-a1.moving_blowups-a1.local_comparison-a1.retraction_comparison-a1`
- Child key: `measure_subadditive`
- Declaration: `Submission.dimred_mbl_lc_rc_measure_le_add_of_closed`
- Exact Lean type: `∀ (P n : ℕ) (V F : Set (Euclid P)) (X X₁ X₂ : GeometricCurrentOn V n) (R R₁ R₂ : IMRep V n), IsOpen V → R.Represents X → R₁.Represents X₁ → R₂.Represents X₂ → (∀ ω : TestFormOn V n, X ω = X₁ ω + X₂ ω) → IsClosed F → F ⊆ V → R.measure F ≤ R₁.measure F + R₂.measure F`

## Sibling prerequisites

- `root.density_one_implies_regular-a1.imrep_mass_and_support-a1`
- `root.compactness_of_minimizing_currents-a1.local_comparison-a1.mass_triangle-a1`
- `root.compactness_of_minimizing_currents-a1.local_comparison-a1.compact_outer_bound-a1`

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
