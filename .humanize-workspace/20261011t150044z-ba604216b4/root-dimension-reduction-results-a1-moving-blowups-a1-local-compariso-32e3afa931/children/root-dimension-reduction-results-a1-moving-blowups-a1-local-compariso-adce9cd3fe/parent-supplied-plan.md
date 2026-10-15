# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.dimension_reduction_results-a1.moving_blowups-a1.local_comparison-a1.index_comparison-a1.cycle-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-dimension-reduction-results-a1-moving-blowups-a1-local-compariso-adce9cd3fe/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.dimension_reduction_results-a1.moving_blowups-a1.local_comparison-a1.index_comparison-a1`
- Child key: `cycle`
- Declaration: `Submission.dimred_mbl_lc_ic_cycle`
- Exact Lean type: `∀ (P m : ℕ) (F : Set (Euclid P)) (C S Ŷ : GeometricCurrentOn (univ : Set (Euclid P)) (m + 1)), IsCompact F → IsIntegerMultiplicity C → IsIntegerMultiplicity S → S.boundary = C.boundary → (S - C).support ⊆ F → IsIntegerMultiplicity Ŷ → Ŷ.boundary = 0 → Ŷ.support ⊆ F → ∃ Y : GeometricCurrentOn (univ : Set (Euclid P)) (m + 1), IsIntegerMultiplicity Y ∧ Y.boundary = 0 ∧ IsCompact Y.support ∧ Y.support ⊆ F ∧ ∀ ω : TestFormOn (univ : Set (Euclid P)) (m + 1), Y ω = (S - C) ω + Ŷ ω`

## Sibling prerequisites

- `root.density_and_tangent_cones-a1.vanish_off_support-a1`
- `root.compactness_of_minimizing_currents-a1.im_calculus-a1`
- `root.regular_set_dense-a1.constant_multiplicity_reduction-a1.support_of_vanishing-a1`

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
