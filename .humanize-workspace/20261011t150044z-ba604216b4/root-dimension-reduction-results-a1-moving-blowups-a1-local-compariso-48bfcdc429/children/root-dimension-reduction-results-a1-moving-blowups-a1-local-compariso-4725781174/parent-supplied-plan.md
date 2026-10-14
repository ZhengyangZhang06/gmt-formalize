# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.dimension_reduction_results-a1.moving_blowups-a1.local_comparison-a1.retraction_comparison-a1.cycle_competitor-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-dimension-reduction-results-a1-moving-blowups-a1-local-compariso-4725781174/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.dimension_reduction_results-a1.moving_blowups-a1.local_comparison-a1.retraction_comparison-a1`
- Child key: `cycle_competitor`
- Declaration: `Submission.dimred_mbl_lc_rc_cycle_competitor`
- Exact Lean type: `∀ (P m : ℕ) (U A W : Set (Euclid P)) (T Z₁ : GeometricCurrentOn U (m + 1)) (X : GeometricCurrentOn (univ : Set (Euclid P)) (m + 1)), IsOpen U → IsMinimizingIn T A → IsOpen W → CompactlyContained W U → IsIntegerMultiplicity X → X.boundary = 0 → IsCompact X.support → X.support ⊆ A ∩ W → (∀ ω : TestFormOn U (m + 1), Z₁ ω = T ω + X (testFormOnInclusion (subset_univ U) (m + 1) ω)) → T.massOn W ≤ Z₁.massOn W`

## Sibling prerequisites

- `root.compactness_of_minimizing_currents-a1.im_calculus-a1`
- `root.density_and_tangent_cones-a1.localize-a1.restrict_im-a1`

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
