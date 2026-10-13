# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.dimension_reduction_results-a1.codimension_one_regularity-a1.simons_regular_cone-a1.offvertex_rep-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-dimension-reduction-results-a1-codimension-one-regularity-a1-sim-b7ab3fcecc/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.dimension_reduction_results-a1.codimension_one_regularity-a1.simons_regular_cone-a1`
- Child key: `offvertex_rep`
- Declaration: `Submission.codim1_cone_offvertex_unit_multiplicity_rep`
- Exact Lean type: `∀ (P m : ℕ) (C : GeometricCurrentOn (univ : Set (Euclid P)) m), 1 ≤ m → IsIntegerMultiplicity C → IsConeCurrent C → (∀ y ∈ C.support, y ≠ 0 → y ∈ regularSet C ∧ HasMassDensity C y 1) → ∃ ξ : Euclid P → MultiVector P m, IsEmbeddedSubmanifold 1 m (C.support \ {0}) ∧ IsOrientation m (C.support \ {0}) ξ ∧ (∀ t : ℝ, 0 < t → ∀ x ∈ C.support \ {0}, t • x ∈ C.support \ {0}) ∧ (∀ K : Set (Euclid P), IsCompact K → μHE[m] ((C.support \ {0}) ∩ K) ≠ ∞) ∧ ∀ ω : TestFormOn (univ : Set (Euclid P)) m, C ω = ∫ x in C.support \ {0}, ξ x ((ω : DifferentialForm (Euclid P) m) x) ∂μHE[m]`

## Sibling prerequisites

- `root.dimension_reduction_results-a1.codimension_one_regularity-a1.simons_regular_cone-a1.density_one_local_rep-a1`
- `root.density_and_tangent_cones-a1.vanish_off_support-a1`
- `root.half_space_cone_lies_in_boundary-a1.cone_measure_homogeneous-a1.cone_pullback_identity-a1`
- `root.density_one_implies_regular-a1.imrep_mass_and_support-a1.unit_orientation_duality-a1`
- `root.regular_set_dense-a1.integer_combination-a1.orientation_sign-a1`
- `root.minimizing_implies_stationary-a1.chart_tangent_space-a1`
- `root.dimension_reduction_results-a1.regular_point_density-a1.bilipschitz_measure-a1`

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
