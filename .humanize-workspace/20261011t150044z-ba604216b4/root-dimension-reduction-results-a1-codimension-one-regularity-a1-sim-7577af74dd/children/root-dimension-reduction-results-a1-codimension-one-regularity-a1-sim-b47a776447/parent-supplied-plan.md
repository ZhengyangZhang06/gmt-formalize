# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.dimension_reduction_results-a1.codimension_one_regularity-a1.simons_regular_cone-a1.density_one_local_rep-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-dimension-reduction-results-a1-codimension-one-regularity-a1-sim-b47a776447/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.dimension_reduction_results-a1.codimension_one_regularity-a1.simons_regular_cone-a1`
- Child key: `density_one_local_rep`
- Declaration: `Submission.codim1_density_one_regular_local_rep`
- Exact Lean type: `∀ (P m : ℕ) (U : Set (Euclid P)) (T : GeometricCurrentOn U m) (y : Euclid P), 1 ≤ m → IsOpen U → y ∈ regularSet T → HasMassDensity T y 1 → ∃ ρ₀ : ℝ, 0 < ρ₀ ∧ ball y ρ₀ ⊆ U ∧ ∀ ρ : ℝ, 0 < ρ → ρ ≤ ρ₀ → ∃ ξ : Euclid P → MultiVector P m, IsEmbeddedSubmanifold 1 m (T.support ∩ ball y ρ) ∧ IsOrientation m (T.support ∩ ball y ρ) ξ ∧ μHE[m] (T.support ∩ ball y ρ) ≠ ∞ ∧ ∀ ω : TestFormOn U m, tsupport (ω : DifferentialForm (Euclid P) m) ⊆ ball y ρ → T ω = ∫ x in T.support ∩ ball y ρ, ξ x ((ω : DifferentialForm (Euclid P) m) x) ∂μHE[m]`

## Sibling prerequisites

- `root.density_one_implies_regular-a1.imrep_mass_and_support-a1.unit_orientation_duality-a1`
- `root.minimizing_implies_stationary-a1.chart_tangent_space-a1`
- `root.dimension_reduction_results-a1.regular_point_density-a1.bilipschitz_measure-a1`

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
