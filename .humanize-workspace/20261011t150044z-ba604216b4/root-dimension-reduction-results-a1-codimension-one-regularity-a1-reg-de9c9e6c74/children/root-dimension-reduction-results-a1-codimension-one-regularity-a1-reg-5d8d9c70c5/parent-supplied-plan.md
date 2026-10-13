# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.dimension_reduction_results-a1.codimension_one_regularity-a1.region_density_one-a1.local_unit_rep-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-dimension-reduction-results-a1-codimension-one-regularity-a1-reg-5d8d9c70c5/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.dimension_reduction_results-a1.codimension_one_regularity-a1.region_density_one-a1`
- Child key: `local_unit_rep`
- Declaration: `Submission.codim1_rdo_local_unit_representation`
- Exact Lean type: `∀ (P n : ℕ) (U N E : Set (Euclid P)) (ξN : Euclid P → MultiVector P (n + 1)) (T : GeometricCurrentOn U n) (x : Euclid P), 1 ≤ n → IsOpen U → InClassO n U N ξN → MeasurableSet E → E ⊆ N ∩ U → IsBoundaryOfRegion T E ξN → IsIntegerMultiplicity T → x ∈ N ∩ U → ∃ (Z₀ M' : Set (Euclid P)) (ξ' : Euclid P → MultiVector P n), IsOpen Z₀ ∧ x ∈ Z₀ ∧ Z₀ ⊆ U ∧ MeasurableSet M' ∧ M' ⊆ Z₀ ∧ CountablyRectifiable n M' ∧ μHE[n] M' ≠ ∞ ∧ AEStronglyMeasurable ξ' (μHE[n].restrict M') ∧ (∀ᵐ w ∂(μHE[n].restrict M'), ∃ Q : Submodule ℝ (Euclid P), IsUnitOrientationOf (ξ' w) Q) ∧ ∀ ω : TestFormOn U n, tsupport (ω : DifferentialForm (Euclid P) n) ⊆ Z₀ → T ω = ∫ w in M', ξ' w ((ω : DifferentialForm (Euclid P) n) w) ∂μHE[n]`

## Sibling prerequisites

- `root.dimension_reduction_results-a1.codimension_one_regularity-a1.region_density_one-a1.graph_chart-a1`
- `root.dimension_reduction_results-a1.codimension_one_regularity-a1.region_density_one-a1.de_giorgi-a1`
- `root.density_one_implies_regular-a1.imrep_mass_and_support-a1.mass_upper_bound-a1`

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
