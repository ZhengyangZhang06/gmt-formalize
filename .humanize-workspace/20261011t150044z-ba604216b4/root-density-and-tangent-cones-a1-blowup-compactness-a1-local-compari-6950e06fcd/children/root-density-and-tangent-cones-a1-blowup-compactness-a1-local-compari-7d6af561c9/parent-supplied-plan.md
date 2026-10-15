# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.density_and_tangent_cones-a1.blowup_compactness-a1.local_comparison-a1.retraction_comparison-a1.cycle_competitor-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-density-and-tangent-cones-a1-blowup-compactness-a1-local-compari-7d6af561c9/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.density_and_tangent_cones-a1.blowup_compactness-a1.local_comparison-a1.retraction_comparison-a1`
- Child key: `cycle_competitor`
- Declaration: `Submission.dtc_bc_lc_rc_cycle_competitor`
- Exact Lean type: `∀ (P m : ℕ) (U A W K : Set (Euclid P)) (S : GeometricCurrentOn U (m + 1)) (X : GeometricCurrentOn (univ : Set (Euclid P)) (m + 1)), IsOpen U → IsMinimizingIn S A → IsOpen W → CompactlyContained W U → IsIntegerMultiplicity X → X.boundary = 0 → IsCompact K → X.support ⊆ K → K ⊆ A ∩ W → S.massOn W ≤ (S - (0 - X.restrictDomain (subset_univ U))).massOn W`

## Sibling prerequisites

- `root.compactness_of_minimizing_currents-a1.im_calculus-a1`
- `root.density_and_tangent_cones-a1.localize-a1.restrict_im-a1`
- `root.density_and_tangent_cones-a1.vanish_off_support-a1`
- `root.regular_set_dense-a1.constant_multiplicity_reduction-a1.support_of_vanishing-a1`

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
