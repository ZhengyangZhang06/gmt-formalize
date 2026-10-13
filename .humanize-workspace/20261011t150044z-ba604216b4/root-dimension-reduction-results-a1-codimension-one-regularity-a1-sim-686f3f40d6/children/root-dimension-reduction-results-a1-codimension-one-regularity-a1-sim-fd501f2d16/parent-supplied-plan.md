# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.dimension_reduction_results-a1.codimension_one_regularity-a1.simons_regular_cone-a1.area_comparison-a1.piece_pushforward-a1.unit_piece_current-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-dimension-reduction-results-a1-codimension-one-regularity-a1-sim-fd501f2d16/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.dimension_reduction_results-a1.codimension_one_regularity-a1.simons_regular_cone-a1.area_comparison-a1.piece_pushforward-a1`
- Child key: `unit_piece_current`
- Declaration: `Submission.codim1_ac_pp_unit_rectifiable_current`
- Exact Lean type: `∀ (P m : ℕ) (M : Set (Euclid P)) (η : Euclid P → MultiVector P m), MeasurableSet M → CountablyRectifiable m M → (∀ K : Set (Euclid P), IsCompact K → μHE[m] (M ∩ K) ≠ ∞) → AEStronglyMeasurable η (μHE[m].restrict M) → (∀ᵐ y ∂(μHE[m].restrict M), ∃ Q : Submodule ℝ (Euclid P), HasApproximateTangentSpaceAt m M y Q ∧ IsUnitOrientationOf (η y) Q) → ∃ D : GeometricCurrentOn (univ : Set (Euclid P)) m, IsIntegerMultiplicity D ∧ (∀ ω : TestFormOn (univ : Set (Euclid P)) m, Integrable (fun y => η y ((ω : DifferentialForm (Euclid P) m) y)) (μHE[m].restrict M) ∧ D ω = ∫ y in M, η y ((ω : DifferentialForm (Euclid P) m) y) ∂μHE[m]) ∧ ∀ W' : Set (Euclid P), D.massOn W' ≤ μHE[m] (M ∩ W')`

## Sibling prerequisites

- `root.density_and_tangent_cones-a1.localize-a1.imrep_current-a1`
- `root.regular_components_are_minimizing-a1.restriction_integer_multiplicity-a1.action_integrable-a1`
- `root.density_one_implies_regular-a1.imrep_mass_and_support-a1.mass_upper_bound-a1`

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
