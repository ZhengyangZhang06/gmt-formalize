# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.dimension_reduction_results-a1.regular_point_density-a1.mass_identity-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-dimension-reduction-results-a1-regular-point-density-a1-mass-identity-a1/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.dimension_reduction_results-a1.regular_point_density-a1`
- Child key: `mass_identity`
- Declaration: `Submission.dimred_rpd_massOn_eq_mult_measure`
- Exact Lean type: `∀ (P n : ℕ) (U : Set (Euclid P)) (T : GeometricCurrentOn U n) (M W : Set (Euclid P)) (m₀ : ℤ) (ξ : Euclid P → MultiVector P n), IsOpen W → W ⊆ U → MeasurableSet M → ContinuousOn ξ M → (∀ x ∈ M, ∃ Q : Submodule ℝ (Euclid P), IsUnitOrientationOf (ξ x) Q) → μHE[n] (M ∩ W) ≠ ∞ → (∀ ω : TestFormOn U n, tsupport (ω : DifferentialForm (Euclid P) n) ⊆ W → T ω = m₀ * ∫ x in M, ξ x ((ω : DifferentialForm (Euclid P) n) x) ∂μHE[n]) → T.massOn W = (m₀.natAbs : ℝ≥0∞) * μHE[n] (M ∩ W)`

## Sibling prerequisites

- `root.density_one_implies_regular-a1.imrep_mass_and_support-a1.unit_orientation_duality-a1`
- `root.density_one_implies_regular-a1.imrep_mass_and_support-a1.smooth_unit_approximation-a1`

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
