# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.dimension_reduction_results-a1.moving_blowups-a1.local_comparison-a1.index_comparison-a1.region_bound-a1.compact_sum_bound-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-dimension-reduction-results-a1-moving-blowups-a1-local-compariso-3a7a5cb36e/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.dimension_reduction_results-a1.moving_blowups-a1.local_comparison-a1.index_comparison-a1.region_bound-a1`
- Child key: `compact_sum_bound`
- Declaration: `Submission.dimred_mbl_lc_ic_rb_measure_le_add_of_compact`
- Exact Lean type: `∀ (P n : ℕ) (U U' E : Set (Euclid P)) (T Z : GeometricCurrentOn U n) (Y : GeometricCurrentOn (univ : Set (Euclid P)) n) (R RZ : IMRep U n) (RY : IMRep (univ : Set (Euclid P)) n), IsOpen U → IsOpen U' → U' ⊆ U → IsCompact E → E ⊆ U' → R.Represents T → RZ.Represents Z → RY.Represents Y → (∀ ω : TestFormOn U n, tsupport (ω : DifferentialForm (Euclid P) n) ⊆ U' → Z ω = T ω + Y (testFormOnInclusion (subset_univ U) n ω)) → RZ.measure E ≤ R.measure E + RY.measure E`

## Sibling prerequisites

- `root.density_one_implies_regular-a1.imrep_mass_and_support-a1`
- `root.compactness_of_minimizing_currents-a1.local_comparison-a1.compact_outer_bound-a1`
- `root.regular_set_dense-a1.density_eq_multiplicity-a1.imrep_local_finiteness-a1`
- `root.dimension_reduction_results-a1.moving_blowups-a1.local_comparison-a1.index_comparison-a1.region_bound-a1.mixed_mass_triangle-a1`

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
