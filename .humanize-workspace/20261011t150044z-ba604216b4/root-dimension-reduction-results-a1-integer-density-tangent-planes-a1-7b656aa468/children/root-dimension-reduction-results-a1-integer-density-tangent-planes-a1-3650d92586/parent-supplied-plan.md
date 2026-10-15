# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.dimension_reduction_results-a1.integer_density_tangent_planes-a1.cone_constant_density_planar-a1.regular_point_support-a1.submanifold_subset_support-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-dimension-reduction-results-a1-integer-density-tangent-planes-a1-3650d92586/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.dimension_reduction_results-a1.integer_density_tangent_planes-a1.cone_constant_density_planar-a1.regular_point_support-a1`
- Child key: `submanifold_subset_support`
- Declaration: `Submission.idtp_ccd_rps_submanifold_subset_support`
- Exact Lean type: `∀ (P n : ℕ) (U G M : Set (Euclid P)) (T : GeometricCurrentOn U n) (m : ℤ) (ξ : Euclid P → MultiVector P n), IsOpen G → G ⊆ U → m ≠ 0 → IsEmbeddedSubmanifold 1 n M → IsOrientation n M ξ → (∀ K : Set (Euclid P), IsCompact K → K ⊆ G → μHE[n] (M ∩ K) ≠ ∞) → (∀ ω : TestFormOn U n, tsupport (ω : DifferentialForm (Euclid P) n) ⊆ G → T ω = m * ∫ x in M, ξ x ((ω : DifferentialForm (Euclid P) n) x) ∂μHE[n]) → M ∩ G ⊆ T.support`

## Sibling prerequisites

- `root.dimension_reduction_results-a1.regular_point_density-a1.locally_closed-a1`
- `root.dimension_reduction_results-a1.regular_point_density-a1.density_one-a1`
- `root.half_space_cone_lies_in_boundary-a1.imrep_support_eq_measure_support-a1.unit_orientation_nonzero_bounded-a1`

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
