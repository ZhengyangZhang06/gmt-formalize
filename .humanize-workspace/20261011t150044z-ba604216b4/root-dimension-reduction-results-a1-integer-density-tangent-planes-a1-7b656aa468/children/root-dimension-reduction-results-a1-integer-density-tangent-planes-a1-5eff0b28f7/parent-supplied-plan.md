# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.dimension_reduction_results-a1.integer_density_tangent_planes-a1.cone_constant_density_planar-a1.regular_point_support-a1.support_subset_closure-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-dimension-reduction-results-a1-integer-density-tangent-planes-a1-5eff0b28f7/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.dimension_reduction_results-a1.integer_density_tangent_planes-a1.cone_constant_density_planar-a1.regular_point_support-a1`
- Child key: `support_subset_closure`
- Declaration: `Submission.idtp_ccd_rps_support_subset_closure`
- Exact Lean type: `∀ (P n : ℕ) (U G M : Set (Euclid P)) (T : GeometricCurrentOn U n) (m : ℤ) (ξ : Euclid P → MultiVector P n), IsOpen G → G ⊆ U → (∀ ω : TestFormOn U n, tsupport (ω : DifferentialForm (Euclid P) n) ⊆ G → T ω = m * ∫ x in M, ξ x ((ω : DifferentialForm (Euclid P) n) x) ∂μHE[n]) → T.support ∩ G ⊆ closure M`

## Sibling prerequisites

- None.

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
