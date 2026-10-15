# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.dimension_reduction_results-a1.moving_blowups-a1.local_comparison-a1.index_comparison-a1.add_restrict-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-dimension-reduction-results-a1-moving-blowups-a1-local-compariso-d9223591d6/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.dimension_reduction_results-a1.moving_blowups-a1.local_comparison-a1.index_comparison-a1`
- Child key: `add_restrict`
- Declaration: `Submission.dimred_mbl_lc_ic_add_restrict`
- Exact Lean type: `∀ (P n : ℕ) (U : Set (Euclid P)) (T : GeometricCurrentOn U n) (Y : GeometricCurrentOn (univ : Set (Euclid P)) n), IsOpen U → IsIntegerMultiplicity T → IsIntegerMultiplicity Y → ∃ Z : GeometricCurrentOn U n, IsIntegerMultiplicity Z ∧ ∀ ω : TestFormOn U n, Z ω = T ω + Y (testFormOnInclusion (subset_univ U) n ω)`

## Sibling prerequisites

- `root.density_and_tangent_cones-a1.localize-a1.restrict_im-a1`
- `root.compactness_of_minimizing_currents-a1.im_calculus-a1`

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
