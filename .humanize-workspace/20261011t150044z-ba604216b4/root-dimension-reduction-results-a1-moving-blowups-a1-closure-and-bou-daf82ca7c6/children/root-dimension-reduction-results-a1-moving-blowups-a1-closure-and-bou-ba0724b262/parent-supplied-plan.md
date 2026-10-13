# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.dimension_reduction_results-a1.moving_blowups-a1.closure_and_boundary_rectifiability-a1.boundary_im-a1.extension_masses-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-dimension-reduction-results-a1-moving-blowups-a1-closure-and-bou-ba0724b262/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.dimension_reduction_results-a1.moving_blowups-a1.closure_and_boundary_rectifiability-a1.boundary_im-a1`
- Child key: `extension_masses`
- Declaration: `Submission.dmcbr_bim_extension_mass_bounds`
- Exact Lean type: `(∀ (P n : ℕ) (U : Set (Euclid P)) (S : GeometricCurrentOn U n) (ω : TestFormOn U n), Disjoint (tsupport (ω : DifferentialForm (Euclid P) n)) S.support → S ω = 0) → ∀ (P k : ℕ) (U C : Set (Euclid P)) (Y : GeometricCurrentOn (univ : Set (Euclid P)) (k + 1)), IsOpen U → IsCompact C → C ⊆ U → Y.support ⊆ C → Y.mass ≤ (Y.restrictDomain (subset_univ U)).mass ∧ Y.boundary.mass ≤ (Y.restrictDomain (subset_univ U)).boundary.mass`

## Sibling prerequisites

- `root.compactness_of_minimizing_currents-a1.local_comparison-a1.mass_localization-a1`

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
