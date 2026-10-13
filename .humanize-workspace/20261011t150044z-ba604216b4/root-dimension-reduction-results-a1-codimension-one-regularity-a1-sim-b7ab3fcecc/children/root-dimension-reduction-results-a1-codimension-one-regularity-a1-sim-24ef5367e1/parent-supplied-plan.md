# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.dimension_reduction_results-a1.codimension_one_regularity-a1.simons_regular_cone-a1.offvertex_rep-a1.orientation_glue-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-dimension-reduction-results-a1-codimension-one-regularity-a1-sim-24ef5367e1/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.dimension_reduction_results-a1.codimension_one_regularity-a1.simons_regular_cone-a1.offvertex_rep-a1`
- Child key: `orientation_glue`
- Declaration: `Submission.codim1_ovr_orientation_glue`
- Exact Lean type: `∀ (P m : ℕ) (C : GeometricCurrentOn (univ : Set (Euclid P)) m) (M : Set (Euclid P)) (ρ : Euclid P → ℝ) (ξs : Euclid P → Euclid P → MultiVector P m), IsEmbeddedSubmanifold 1 m M → MeasurableSet M → (∀ y ∈ M, 0 < ρ y ∧ IsOrientation m (M ∩ ball y (ρ y)) (ξs y) ∧ μHE[m] (M ∩ ball y (ρ y)) ≠ ∞ ∧ ∀ ω : TestFormOn (univ : Set (Euclid P)) m, tsupport (ω : DifferentialForm (Euclid P) m) ⊆ ball y (ρ y) → C ω = ∫ x in M ∩ ball y (ρ y), ξs y x ((ω : DifferentialForm (Euclid P) m) x) ∂μHE[m]) → ∃ ξ : Euclid P → MultiVector P m, IsOrientation m M ξ ∧ (∀ y ∈ M, ∀ x ∈ M ∩ ball y (ρ y), ξ x = ξs y x) ∧ ∀ y ∈ M, ∀ ω : TestFormOn (univ : Set (Euclid P)) m, tsupport (ω : DifferentialForm (Euclid P) m) ⊆ ball y (ρ y) → C ω = ∫ x in M, ξ x ((ω : DifferentialForm (Euclid P) m) x) ∂μHE[m]`

## Sibling prerequisites

- `root.dimension_reduction_results-a1.codimension_one_regularity-a1.simons_regular_cone-a1.offvertex_rep-a1.submanifold_local-a1`
- `root.density_one_implies_regular-a1.imrep_mass_and_support-a1.unit_orientation_duality-a1`
- `root.regular_set_dense-a1.integer_combination-a1.orientation_sign-a1`
- `root.dimension_reduction_results-a1.regular_point_density-a1.density_one-a1`

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
