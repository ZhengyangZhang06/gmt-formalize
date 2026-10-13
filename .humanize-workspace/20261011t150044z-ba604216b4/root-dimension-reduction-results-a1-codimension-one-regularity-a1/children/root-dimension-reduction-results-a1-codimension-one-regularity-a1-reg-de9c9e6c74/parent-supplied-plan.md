# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.dimension_reduction_results-a1.codimension_one_regularity-a1.region_density_one-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-dimension-reduction-results-a1-codimension-one-regularity-a1-reg-de9c9e6c74/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.dimension_reduction_results-a1.codimension_one_regularity-a1`
- Child key: `region_density_one`
- Declaration: `Submission.codim1_region_density_one_dense`
- Exact Lean type: `∀ (P n : ℕ) (U N E : Set (Euclid P)) (ξN : Euclid P → MultiVector P (n + 1)) (T : GeometricCurrentOn U n), 1 ≤ n → IsOpen U → InClassO n U N ξN → MeasurableSet E → E ⊆ N ∩ U → IsBoundaryOfRegion T E ξN → IsIntegerMultiplicity T → ∀ x ∈ T.support, ∀ ρ : ℝ, 0 < ρ → ∃ y ∈ T.support ∩ ball x ρ, HasMassDensity T y 1`

## Sibling prerequisites

- `root.dimension_reduction_results-a1.codimension_one_regularity-a1.region_support_cycle-a1`
- `root.dimension_reduction_results-a1.codimension_one_regularity-a1.oriented_piece_mass-a1`
- `root.density_one_implies_regular-a1.imrep_mass_and_support-a1.unit_orientation_duality-a1`
- `root.regular_set_dense-a1.integer_combination-a1.orientation_sign-a1`

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
