# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.dimension_reduction_results-a1.moving_blowups-a1.local_comparison-a1.retraction_comparison-a1.mass_domain_compare-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-dimension-reduction-results-a1-moving-blowups-a1-local-compariso-7497990374/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.dimension_reduction_results-a1.moving_blowups-a1.local_comparison-a1.retraction_comparison-a1`
- Child key: `mass_domain_compare`
- Declaration: `Submission.dimred_mbl_lc_rc_massOn_restrict_univ`
- Exact Lean type: `∀ (P n : ℕ) (U G : Set (Euclid P)) (X : GeometricCurrentOn (univ : Set (Euclid P)) n) (Z : GeometricCurrentOn U n), (X.restrictDomain (subset_univ U)).massOn G ≤ X.massOn G ∧ (G ⊆ U → (∀ ω : TestFormOn U n, tsupport (ω : DifferentialForm (Euclid P) n) ⊆ G → X (testFormOnInclusion (subset_univ U) n ω) = Z ω) → X.massOn G ≤ Z.massOn G)`

## Sibling prerequisites

- None.

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
